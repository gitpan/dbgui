#!/net/pvcsserv01/sft/gnu/bin/perl
#!/usr/local/bin/perl
################################################################################
##                                                                            ##
## Author     :  Monty Scroggins                                              ##
## Description:  Perform database commands with a GUI interface               ##
##                                                                            ##
##  Parameters:  none                                                         ##
##                                                                            ##
## +++++++++++++++++++++++++++ Maintenance Log ++++++++++++++++++++++++++++++ ##
## Tue Sep 1 02:30:59 GMT 1998  Monty Scroggins - Script created.  
##    verified to work on RedHat Linux 5.1 and Solaris 2.6        
##
## Mon Oct 9 16:00:54 GMT 1998   Added code to perform db commands other than
##    select statements.  Changed listbox to text widget to accomodate 
##
## Sun Nov 1 18:39:51 GMT 1998  Many Enhancements - Snapshots, Print, Datatypes,
##    Enable/Disable Command Strings, remove/replace table header on queries,
##    Save file requester.   Many bug fixes
##
## Fri Nov 13 00:15:38 GMT 1998 More bug fixes
##
## Mon Jan 25 22:49:59 GMT 1999 Changed filerequester to new getFileName()
##    Also added Optionset calls to set default colors - trimmed 10% :-)
##
## Mon Feb 1 23:21:16 GMT 1999  Added commandtype assoc array to force row/column style
##    for certain "sp_" commands
##
## Sun Feb 21 11:48:14 CST 1999 Added Menubutton "Method" to force any command to be
##    executed with the system isql command even though the output is really ugly  ;-)
##
## Wed Mar 31 19:00:52 CST 1999 Re-wrote handling of multiple result sets.  Now multiple
##    result sets are detected and the header/sort functions are disabled.  Also
##    added Sqsh executable option for comparison
##
## Tue Apr 20 12:02:51 CDT 1999 Various cleaning up....  fixed a bug where the scroll
##    positions were not being restored after a DB command.
##
## Thu Apr 28 19:30:29 CDT 1999 Added clone window....  added functionality to allow
##    saving of the cloned data to a file. Added a datestring to the titlebars to indicate
##    the date/time of the sampled data
##
## Fri May 14 15:15:47 CDT 1999 Fixed problem with search dialog losing the histories
##
## Tue May 18 13:55:06 CDT 1999 Fixed problem where I wasnt displaying the errors returned
##     if an invalid command (for example) was executed on the server..  (no result sets returned)
##
## Tue May 25 17:47:55 CDT 1999  Moved the row/column counters to the top.  Makes for a smaller
##     and more efficient display.
## 
## Wed Jun 9 12:11:05 CDT 1999  Added the small change to display pound symbols instead of the
##     actual text for the password entry.  Changed the busy indicator to a simple colored frame
##     for simplicity.
##
## Wed Jun 16 17:54:50 CDT 1999  Made some minor - mostly cosmetic changes.  Fixed a bug where
##     the sql command was being printed twice in a save file.  
##
## Tue Jun 22 17:14:03 CDT 1999  Added the checkpoint file as an argument to allow pre-defined
##     menu histories to be defined and kept in separate database files.
##
## Fri Jul 9 14:05:10 CDT 1999 Version 2.0.  Ported to DBI/DBD!. Fixed a bug in the handling of 
##     sql strings which include special characters.  Some small cosmetic changes.  Moved the
##     row/column counters towards the bottom (again)... 
##
##
################################################################################

#the current version
local $VERSION="2.0";

=head1 NAME

DBGUI - a database server graphical interface. 

=head1 DESCRIPTION

DBGUI features:

=over 4

Perform any SQL command.

Save the SQL results to a file.

Perform incremental or standard searches or the SQL results.

Keep a history of _all_ SQL commands and parameters.

Sort (normal, numerical and reverse) on any column of the SQL results.

Print the SQL results to a printer.

Quick command line clear and restore for easy command line generation/pasting.

"Clone" the results to a new display window for comparisons etc.

Utilize the DBI/DB libraries or isql/sqsh binaries for the queries.

Maintain four complete configuration "snapshots" for easy retrieval.

Reload the last set of parameters on startup.

Interactively enable and disable any or all of three different command lines for execution.  All of
the 'active' command lines are concatenated, therefore the three command entry lines can be used to
quickly eliminate/add command parameters to an existing command.

Display the column data type in each column header.

Display the column data width in each column header.

Solicit and quickly popup a list of the system datatypes. 

Colored busy indicator (red/green) to indicate if the DBGUI is waiting on results from the DB server.

The date/time of command execution is captured in the title bar.

The checkpoint file can be specified as an argument. Allowing pre-defined menu histories to be defined

More probably....  :-)

=back

=head1 PREREQUISITES

This script requires the following Perl Modules:

=over 4

C<Tk Toolkit>

C<DBI>

C<DBD>

C<Sort::Fields>

C<Tk::HistEntry>

C<Tk::PrintDialog>

=back


=pod SCRIPT CATEGORIES

CPAN/Administrative
Fun/Educational

=cut

use Tk;
#entry widget with history menu
use Tk::HistEntry;
#new DBI/DBD package
use DBI;

#sort library 
use Sort::Fields;
use Tk::PrintDialog;
use Text::Wrap;

#perl variables
$|=1; # set output buffering to off
$[ = 0; # set array base to 0
$, = ' '; # set output field separator
$\ = "\n"; # set output record separator

#The colors and such
local $txtbackground="snow2";
local $txtforeground="black";
local $background="bisque3";
local $troughbackground="bisque4";
local $buttonbackground="tan";
local $headerbackground='#f0f0c7';
local $headerforeground='#900000';
local $datatypeforeground='#704030';
local $winfont=$listboxfont="8x13bold";
local $trbgd="bisque4";
local $labelbackground='bisque2';
local $rowcolcolor='#002030';
local $entrywidth=11;
local $toplabelwidth=12;
local $tophistentrywidth=9;
local $buttonwidth=4;
local $ypad=4;
local $busy="Ready";
local $busycolor="red2",
local $unbusycolor='#009f00',
local $savedialogcolor="#caC2BBBBA7A7";
local $histlimit=100;

#######################################################################
#DBD module specific settings.  
# in an attempt to make this program as portable as possible, I am setting
# some variables to be used to define specific parameters that have to be
# used for a given DBD module.   Hopefully these will apply to most of the
# DBD modules and you can simply change these values.
#
#the servertype is used to tell DBI which interface module to load.  
$servertype="Sybase";

#the DBD client error handler to startup
$errorhandler="syb_err_handler";

#the DBD client data types definition
$dbtypes="syb_types";

#the result types function
$resulttypes="syb_result_type";

#ctlib defined datatypes as defined in cstypes.h 
#a MAX of 5 characters!
%dbdatatypes=qw(  
   -1     illeg
    0     char
    1     bin
    2     lchar
    3     lbin
    4     text
    5     image
    6     tyint
    7     smint
    8     int
    9     real
   10     float
   11     bit
   12     date
   13     datd4
   14     money
   15     mony4
   16     numer
   17     decim
   18     varch
   19     varbn
   20     long
   21     sens
   22     bdry
   23     void
   24     ushrt
);

#######################################################################


#if these binaries are on the path, set to just "isql" or "sqsh"
#I set these to the complete paths because many of my users do not
#have the nfs filesystem which contains these binaries on their
#search paths..

#the path to the isql binary
local $isqlbinary="/net/pvcsserv01/sft/sybase/bin/isql";
#the path to the sqsh binary
local $sqshbinary="/net/pvcsserv01/usr/tools/sqsh";


#the sql command used to extract the defined datatypes from the database
local $dbtypescmd="select type,length,name from systypes";

#available printers
local @printers=("hp4si-678-1158","Print-to-File");

#set to the postscript printing program.  We use a2ps
local $psprint="/net/pvcsserv01/sft/gnu/opt/a2ps/bin/a2ps";

#a list of variables that are saved in the checkpoint file
local @variablelist=qw(
dbserver  
dbuser
dbpass
dbuse
maxrowcount
querystring1
querystring2
querystring3
qsactive1
qsactive2
qsactive3
snapshot0
snapshot1
snapshot2
snapshot3
snapshot4
srchstring
method
);

#a list of arrays that are saved in the checkpoint file
local @arraylist=qw(
dbservhist
dbuserhist
dbpasshist
dbusehist 
queryhist1
queryhist2
queryhist3
searchhist
);

#Set specific column widths for the columns that have expandable data. ex - 
#date and time values are expanded into long english type strings by the server even
#though the length of the column might only be 4 bytes.
#8=integer 10=float 12=datetime 13=datetime4 1=binary (passwords)
#note - these values do not show up in the data pane, the original widths are used for this. 
#     but the widths of the columns will be set to this value
local %specialcollengths=qw(
8   10
10  20
12  19
13  19
1   60
);

#check the arguments.  If one is given it has to be checkpoint file to load.  If none
#is given, use the home directory
$checkf="$ARGV[0]";
$checkpointfile="$ENV{HOME}/.dbgui";

#if the checkpoint file is not found and a real value has been passed as ARGV0
if (!-f $checkf && $checkf) {
   $checkpointfile=$checkf;
   }

#if the checkpoint file is found in the home directory, use it
if (-f "$ENV{HOME}\/$checkf") {
   $checkpointfile="$ENV{HOME}/$checkf";
   }

#if the checkpoint file contains a full path, use it
if (-f "$checkf") {
   $checkpointfile="$checkf";
   }

#if it just doesnt exist, prompt to create it
if (!-f $checkpointfile) {
   $confirmwin->destroy if Exists($confirmwin);
   $confirmwin = Tk::MainWindow->new;
   $confirmwin->withdraw;
   local $confirmbox=$confirmwin->messageBox(
      -type=>'OKCancel',
      -bg=>$background,
      -font=>'8x13bold',
      -title=>"Prompt",
      -text=>"The Checkpoint file \"$checkpointfile\" does not exist...\nCreate it??",
      );
   if ($confirmbox ne "Ok") {
       exit;
      }#
   }#if ! -f checkf

#if the checkpoint file exists, execute it to startup in the same state as when it was shutdown
if (-e $checkpointfile) {
  require ("$checkpointfile");
  }

#startup with the last data in the widgets
local $snapshot=0;

#a list of potentially dangerous commands that should be operator confirmed before being executed
local @dangercmds=qw(
update
delete
truncate
drop
shutdown
kill
);

#reset the data counters
local $dbrowcount=0;
local $dbcolcount=0;

#set the initial maxrowcount to 1000 if not defined  a nice number
if (!$maxrowcount) {
   local $maxrowcount=1000;
   };

#                                       Main Window     
#------------------------------------------------------------------------------------------
#
$LW = new  MainWindow (-title=>"DBGUI $VERSION  [$checkpointfile]");
#set some inherited default colors
$LW->optionAdd("*background","$background"); 
$LW->optionAdd("*foreground","$txtforeground"); 
$LW->optionAdd("*highlightBackground", "$savedialogcolor");
$LW->optionAdd("*Button.Background", "$buttonbackground");
$LW->optionAdd("*activeForeground", "$txtforeground");
$LW->optionAdd("*Menubutton*Background", "$buttonbackground");
$LW->optionAdd("*Menubutton*activeForeground", "$txtforeground");
$LW->optionAdd("*Label*Background", "$labelbackground");
$LW->optionAdd("*troughColor", "$troughbackground");
$LW->optionAdd("*borderWidth", "1");
$LW->optionAdd("*highlightThickness", "0");
$LW->optionAdd("*font", "8x13bold");
$LW->optionAdd("*label*relief", "flat");
$LW->optionAdd("*frame*relief", "flat");
$LW->optionAdd("*button*relief", "raised");
$LW->optionAdd("*Checkbutton*relief", "raised");
$LW->optionAdd("*optionmenu*relief", "raised");

#set an initial size
$LW->minsize(85,2);
$LW->geometry("85x3");

#label frame 
$listframeall=$LW->Frame(
   -borderwidth=>'1',
   -relief=>'sunken',
   )->pack(
      -fill=>'both',
      -expand=>1,
      -pady=>0,
      -padx=>0,
      -side=>'top',
      );

$buttonframe=$LW->Frame(
   )->pack(
      -fill=>'x',
      -pady=>0,
      -padx=>0,
      -side=>'bottom',
      );

$rowcolframe=$LW->Frame(
   )->pack(
      -fill=>'x',
      -pady=>0,
      -padx=>0,
      -side=>'bottom',
      );


#label frame for all of the labels and histentrys at the top
$labelframe=$listframeall->Frame(
   -borderwidth=>'0',
   -relief=>'raised',
   )->pack(
      -fill=>'x',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'top',
      );
    
$labelent1=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );

$labelent2=$labelframe->Frame(
   #-borderwidth=>'1',
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,    
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );
    
$labelent3=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );
    
$labelent4=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );
    
$labelent5=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );    

$labelent6=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );

$labelent7=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );
      
$busymarker=$labelframe->Frame(
   -relief=>'raised',
   -width=>16,
   -height=>16,
   -background=>$unbusycolor,
   )->pack(
      -expand=>0,    
      -pady=>2,
      -padx=>2,
      -side=>'right',
      );    
      
$labelent8=$labelframe->Frame(
   -relief=>'raised',
   -background=>$labelbackground,
   )->pack(
      -fill=>'y',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -side=>'left',
      );
        
$listframe1=$listframeall->Frame(
   -borderwidth=>'0',
   -relief=>'sunken',
   )->pack(
      -fill=>'both',
      -expand=>1,    
      -pady=>0,
      -padx=>0,
      );
    
#the labels frame across the top
##############################################    
#                              query strings
$labelent1->Label(
   -text=>'DB Server',
   -width=>$toplabelwidth,
   )->pack(
      -fill=>'x', 
      -side=>'top',
      -padx=>0,
      -pady=>0,
      -expand=>0,
      );

$servhistframe=$labelent1->Frame(
   -relief=>'sunken',
   )->pack(
      -side=>'bottom',
      -expand=>0,
      -pady=>0,
      -padx=>1,
      );
     
$dbserventry=$servhistframe->HistEntry(
   -relief=>'flat',
   -textvariable=>\$dbserver,
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -background=> 'white',
   -width=>$tophistentrywidth,
   -limit=>$histlimit,
   -dup=>0,
   -match=>0,  
   -command=>sub{@dbservhisttemp=$dbserventry->history;},
   -justify=>'center',
   )->pack(
      -side=>'left',
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -fill=>'x',
      );

$dbserventry->bind('<Return>'    => \&check_cmd); 
$dbserventry->bind('<Up>'        => sub { $dbserventry->historyUp });
$dbserventry->bind('<Control-p>' => sub { $dbserventry->historyUp });
$dbserventry->bind('<Down>'      => sub { $dbserventry->historyDown });
$dbserventry->bind('<Control-n>' => sub { $dbserventry->historyDown });
$dbserventry->history([@dbservhist]);

$labelent2->Label(
   -text=>'Username',
   -width=>$toplabelwidth,
   )->pack(
      -fill=>'y', 
      -padx=>0,
      -pady=>0,
      -expand=>0,
      -side=>'top',
      );

$userhistframe=$labelent2->Frame(
   -relief=>'sunken',
   )->pack(
      -side=>'bottom',
      -expand=>0,
      -pady=>0,
      -padx=>1,
      );
     
$dbuserentry=$userhistframe->HistEntry(
   -relief=>'flat',
   -textvariable=>\$dbuser,
   -highlightcolor=>'black',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -borderwidth=>0,
   -background=> 'white',
   -width=>$tophistentrywidth,
   -limit=>$histlimit,  
   -dup=>0,
   -match=>0,  
   -justify=>'center',
   -command=>sub{@dbuserhisttemp=$dbuserentry->history;},
   )->pack(  
      -expand=>0,
      -padx=>0,
      -pady=>0,
      -fill=>'x',
      );

$dbuserentry->bind('<Return>'    => \&check_cmd); 
$dbuserentry->bind('<Up>'        => sub { $dbuserentry->historyUp });
$dbuserentry->bind('<Control-p>' => sub { $dbuserentry->historyUp });
$dbuserentry->bind('<Down>'      => sub { $dbuserentry->historyDown });
$dbuserentry->bind('<Control-n>' => sub { $dbuserentry->historyDown });
$dbuserentry->history([@dbuserhist]);

$labelent3->Label(
   -text=>'Password',
   -width=>$toplabelwidth,
   )->pack(
      -fill=>'y', 
      -side=>'top',
      -padx=>0,
      -pady=>0,
      -expand=>0,
      );

$passhistframe=$labelent3->Frame(
   -relief=>'sunken',
   )->pack(
      -side=>'bottom',
      -expand=>0,
      -pady=>0,
      -padx=>1,         
      );
     

$dbpassentry=$passhistframe->HistEntry(
   -relief=>'flat',
   -textvariable=>\$dbpass,
   -highlightcolor=>'black',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -borderwidth=>0,
   -background=> 'white',
   -width=>$tophistentrywidth,
   -limit=>$histlimit,  
   -dup=>0,
   -match=>0,  
   -justify=>'center',
   -show => '#',
   -command=>sub{@dbpasshisttemp=$dbpassentry->history;},
   )->pack(
      -expand=>0,
      -padx=>0,
      -pady=>0,        
      -fill=>'x',
      );
    
$dbpassentry->bind('<Return>'    => \&check_cmd); 
$dbpassentry->bind('<Up>'        => sub { $dbpassentry->historyUp });
$dbpassentry->bind('<Control-p>' => sub { $dbpassentry->historyUp });
$dbpassentry->bind('<Down>'      => sub { $dbpassentry->historyDown });
$dbpassentry->bind('<Control-n>' => sub { $dbpassentry->historyDown });
$dbpassentry->history([@dbpasshist]);


$labelent4->Label(
   -text=>'Use DB',
   -width=>$toplabelwidth,
   )->pack(
      -fill=>'y', 
      -side=>'top',
      -padx=>0,
      -pady=>0,
      -expand=>0,
      );

$dbusehistframe=$labelent4->Frame(
   -relief=>'sunken',
   )->pack(
      -side=>'bottom',
      -expand=>0,
      -pady=>0,
      -padx=>1,         
      );
     
$dbuseentry=$dbusehistframe->HistEntry(
   -relief=>'flat',
   -textvariable=>\$dbuse,
   -highlightcolor=>'black',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -borderwidth=>0,
   -background=> 'white',
   -width=>$tophistentrywidth,
   -limit=>$histlimit,  
   -justify=>'center',
   -dup=>0,
   -match=>0,  
   -command=>sub{@dbusehisttemp=$dbuseentry->history;},
   )->pack(
      -expand=>0,
      -padx=>0,
      -pady=>0, 
      -fill=>'x',
      );
      
$dbuseentry->bind('<Return>'    => \&check_cmd); 
$dbuseentry->bind('<Up>'        => sub { $dbuseentry->historyUp });
$dbuseentry->bind('<Control-p>' => sub { $dbuseentry->historyUp });
$dbuseentry->bind('<Down>'      => sub { $dbuseentry->historyDown });
$dbuseentry->bind('<Control-n>' => sub { $dbuseentry->historyDown });
$dbuseentry->history([@dbusehist]);

$labelent5->Label(
   -text=>'Max Rows',
   -width=>$toplabelwidth, 
   )->pack(
      -fill=>'y',  
      -side=>'top',
      -padx=>0,
      -pady=>0,
      );
   
$maxrowentry=$labelent5->Entry(
   -textvariable=>\$maxrowcount,
   -width=>$toplabelwidth,
   -background=>'white',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',  
   -relief=>'sunken',
   -justify=>'center',
   )->pack(
      -side=>'bottom',
      -expand=>1,
      -padx=>1,
      -pady=>0,
      -fill=>'y',
      );
    
$maxrowentry->bind('<Return>'=>\&check_cmd); 

$labelent6->Label(
   -text=>'Snapshot',
   -width=>$toplabelwidth, 
   )->pack(
      -fill=>'y',  
      -side=>'top',
      -padx=>0,
      -pady=>0,
      );

$labelent6->Label(
   -textvariable=>\$snapshot,
   -width=>1,
   -background=>$txtbackground,
   -relief=>'sunken',
   )->pack(
      -side=>'right',
      -expand=>1,
      -padx=>1,
      -pady=>1,
      -fill=>'y',
      );

$snapscale=$labelent6->Scale(
   -variable=>\$snapshot,
   -orient=>'horizontal',
   -label=>'',
   -from=>0,
   -to=>4,
   -length=>86,    
   -troughcolor=>$txtbackground,
   -sliderlength=>12,
   -width=>19,
   -showvalue=>0,
   -command=>sub{&run_snapshot("$snapshot");},
   )->pack(
      -side=>'bottom',
      -padx=>0,
      -pady=>0,
      -fill=>'y', 
      );
$snapscale->bind('<Return>'=> \&check_cmd); 

$labelent7->Label(
   -text=>'Method',
   -width=>$toplabelwidth,
   )->pack(
      -fill=>'y', 
      -side=>'top',
      -padx=>0,
      -expand=>0,
      );

$methodframe=$labelent7->Frame(
   -relief=>'sunken',
   -height=>20,
   -borderwidth=>1,
   )->pack(
      -side=>'bottom',
      -expand=>1,
      -pady=>0,
      -padx=>0,
      -fill=>'x',
      );

$methodmenu=$methodframe->Menubutton(
   -textvariable=>\$method,
   -relief=>'sunken',
   -indicatoron=>1,
   -borderwidth=>0,
   -background=>$txtbackground,
   )->pack(
      -side=>'bottom',
      -padx=>0,
      -pady=>0,
      -fill=>'x',
      );

$methodmenu->command(
   -label=>'DBI/DBD Libraries',
   -command=>sub{$method="DBI/DBD";},
   -background=>$background,
   );

$methodmenu->command(
   -label=>'Isql Command',
   -command=>sub{$method="Isql";},
   -background=>$background,
   );
   
$methodmenu->command(
   -label=>'Sqsh Command',
   -command=>sub{$method="Sqsh";},
   -background=>$background,
   );


##############################################
#query strings

$qs1frame=$listframe1->Frame(
   -relief=>'sunken',
   -highlightthickness=>0,
   )->pack(
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -fill=>'x',
      );
      
$clr1=$qs1frame->Button(
   -text=>"C",
   -width=>1,
   -command=>sub{
      if ($querystring1 ne "") {
         $qs1sav=$querystring1;
         $querystring1="";
         };},
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -fill=>'y',
      );     

#use button three to restore the clear operation
$clr1->bind('<Button-3>'=>sub{if ($qs1sav) {$querystring1=$qs1sav}});

$qscheck1=$qs1frame->Checkbutton(
   -variable=>\$qsactive1,
   -text=>"Sel",
   -background=>$buttonbackground,
   -borderwidth=>1,
   -selectcolor=>'red4',
   -width=>4,
   -offvalue=>0,
   -onvalue=>1,
   -command=>sub{&act_deactivate("qsentry1","qsactive1")},
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -fill=>'y',
      );     

$qsentry1=$qs1frame->HistEntry(
   -relief=>'flat',
   -textvariable=>\$querystring1,
   -highlightcolor=>'black',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -borderwidth=>0,
   -background=> 'white',
   -limit=>$histlimit,
   -dup=>1,
   -match=>0,
   -command=>sub{@queryhist1temp=$qsentry1->history;},
   )->pack(
      -fill=>'both',
      -expand=>1,
      -pady=>1,
      );

$qsentry1->bind('<Return>'    => \&check_cmd); 
$qsentry1->bind('<Up>'        => sub { $qsentry1->historyUp });
$qsentry1->bind('<Control-p>' => sub { $qsentry1->historyUp });
$qsentry1->bind('<Down>'      => sub { $qsentry1->historyDown });
$qsentry1->bind('<Control-n>' => sub { $qsentry1->historyDown });
$qsentry1->history([@queryhist1]);

$qs2frame=$listframe1->Frame(
   -relief=>'sunken',
   )->pack(
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -fill=>'x',         
      );
         
$clr2=$qs2frame->Button(
   -text=>"C",
   -width=>1,
   -command=>sub{
      if ($querystring2 ne "") {
         $qs2sav=$querystring2;
         $querystring2="";
         };},
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -fill=>'y',
      );   
      
#use button three to restore the clear operation
$clr2->bind('<Button-3>'=>sub{if ($qs2sav) {$querystring2=$qs2sav}});

$qscheck2=$qs2frame->Checkbutton(
   -variable=>\$qsactive2,
   -relief=>'raised',
   -text=>"Sel",
   -background=>$buttonbackground,
   -selectcolor=>'red4',
   -width=>4,
   -offvalue=>0,
   -onvalue=>1,
   -command=>sub{&act_deactivate("qsentry2","qsactive2")},
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -fill=>'y',
      );       

$qsentry2=$qs2frame->HistEntry(
   -relief=>'flat',
   -textvariable=>\$querystring2,
   -highlightcolor=>'black',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -borderwidth=>0,
   -background=> 'white',
   -limit=>$histlimit,
   -dup=>1,
   -match=>0,
   -command=>sub{@queryhist2temp=$qsentry2->history;},
   )->pack(
      -fill=>'both',
      -expand=>1,
      -pady=>1,
      );
    
$qsentry2->bind('<Return>'    => \&check_cmd); 
$qsentry2->bind('<Up>'        => sub { $qsentry2->historyUp });
$qsentry2->bind('<Control-p>' => sub { $qsentry2->historyUp });
$qsentry2->bind('<Down>'      => sub { $qsentry2->historyDown });
$qsentry2->bind('<Control-n>' => sub { $qsentry2->historyDown });
$qsentry2->history([@queryhist2]);

$qs3frame=$listframe1->Frame(
   -relief=>'sunken',
   )->pack(
      -expand=>0,
      -pady=>0,
      -padx=>0,
      -fill=>'x',         
      );
         
$clr3=$qs3frame->Button(
   -text=>"C",
   -width=>1,
   -command=>sub{
      if ($querystring3 ne "") {
         $qs3sav=$querystring3;
         $querystring3="";
         };},
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -fill=>'y',
      );         
#use button three to restore the clear operation
$clr3->bind('<Button-3>'=>sub{if ($qs3sav) {$querystring3=$qs3sav}});

$qscheck3=$qs3frame->Checkbutton(
   -variable=>\$qsactive3,
   -relief=>'raised',
   -text=>"Sel",
   -background=>$buttonbackground,
   -selectcolor=>'red4',
   -width=>4,
   -offvalue=>0,
   -onvalue=>1,
   -command=>sub{&act_deactivate("qsentry3","qsactive3")},
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -fill=>'y',
      );       

$qsentry3=$qs3frame->HistEntry(
   -relief=>'flat',
   -textvariable=>\$querystring3,
   -highlightcolor=>'black',
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -borderwidth=>0,
   -background=> 'white',
   -limit=>$histlimit,
   -dup=>1,
   -match=>0,
   -command=>sub{@queryhist3temp=$qsentry3->history;},
   )->pack(
      -fill=>'both',
      -expand=>1,
      -pady=>1,
      );
    
$qsentry3->bind('<Return>'    => \&check_cmd); 
$qsentry3->bind('<Up>'        => sub { $qsentry3->historyUp });
$qsentry3->bind('<Control-p>' => sub { $qsentry3->historyUp });
$qsentry3->bind('<Down>'      => sub { $qsentry3->historyDown });
$qsentry3->bind('<Control-n>' => sub { $qsentry3->historyDown });
$qsentry3->history([@queryhist3]);

#padding for spacing between the query strings and the output Text widget
   $listframe1->Frame(
   -relief=>'sunken',
   -height=>3,    
   )->pack(
      -side=>'top',  
      -padx=>0,
      -pady=>0,
      -expand=>0,
      -fill=>'x',
      );
    
#-----------------------------------------------------------------------------
#                                   data listboxes

$scrolly=$listframe1->Scrollbar(
   -orient=>'vert',
   -elementborderwidth=>1,
   )->pack(
      -side=>'right',
      -fill=>'y',
      );

$scrollx=$listframe1->Scrollbar(
   -orient=>'horiz',
   -elementborderwidth=>1,
   )->pack(
      -side=>'bottom',
      -fill=>'x',
      );
    
$queryheader=$listframe1->Text(
   -xscrollcommand=>['set', $scrollx],
   -relief=>'flat',
   -background=>$headerbackground,
   -foreground=>$headerforeground,
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -setgrid=>'yes',
   -wrap=>'none',  
   -height=>2,
   -exportselection=>1,
   )->pack(
      -fill=>'x',
      -expand=>0,
      -pady=>0,
      -anchor=>'n',
      );

$queryout=$listframe1->Text(
   -yscrollcommand=>['set', $scrolly],
   -xscrollcommand=>['set', $scrollx],
   -relief=>'sunken',
   -background=>$txtbackground,
   -selectforeground=>$txtforeground,
   -selectbackground=>'#c0d0c0',
   -wrap=>'none',
   -height=>14,
   -exportselection=>1, 
   )->pack(
      -fill=>'both',
      -expand=>1,
      -pady=>0,
      );

$scrolly->configure(-command=>['yview', $queryout]);
$scrollx->configure(-command=>\&my_xscroll);

#------------------------------------------------------------------------------------------
#                              bottom row of buttons and labels

$rownumlabel=$rowcolframe->Label(
   -text=>' Rows:',
   -foreground=>$rowcolcolor,
   -background=>$background,
   -justify=>'right'
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>0,
      );

$rowcolframe->Label(
   -textvariable=>\$dbrowcount,
   -width=>8,
   -background=>$txtbackground,
   -foreground=>$rowcolcolor,
   -relief=>'sunken',
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>0,
      -fill=>'y',
      );

$colnumlabel=$rowcolframe->Label(
   -text=>' Cols:',
   -foreground=>$rowcolcolor,
   -background=>$background,
   -justify=>'right'
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>0,
      );

$rowcolframe->Label(
   -textvariable=>\$dbcolcount,
   -width=>8,
   -background=>$txtbackground,
   -foreground=>$rowcolcolor,
   -relief=>'sunken',
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>0,
      -fill=>'y',
      );



$sortframe=$buttonframe->Frame(
   -relief=>'sunken',
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>0,
      -expand=>1,
      -fill=>'x',      
      );
         
$sortlabel=$sortframe->Label(
   -text=>'Sort:',
   -relief=>'flat',
   -width=>6,
   -background=>$background,
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>$ypad,
      );

#the sortby textvariable will be configured after the window is created.
#$sortbyentry=$sortframe->Menubutton(
$sortbyentry=$sortframe->Optionmenu(
   -background=>$buttonbackground,
   -width=>24,
   -command=>\&sortby,
   )->pack(
      -side=>'left',
      -expand=>1,
      -pady=>$ypad,
      -padx=>0,
      -fill=>'both',
      );

$revsortbutton=$sortframe->Checkbutton(
   -variable=>\$reversesort,
   -text=>"Rev",
   -background=>$buttonbackground,
   -borderwidth=>1,
   -selectcolor=>'red4',
   -width=>4,
   -offvalue=>0,
   -onvalue=>1,
   -command=>\&sortby,
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -pady=>$ypad,
      -fill=>'y',
      );     

$numsortbutton=$sortframe->Checkbutton(
   -variable=>\$numsort,
   -text=>"Num",
   -background=>$buttonbackground,
   -borderwidth=>1,
   -selectcolor=>'red4',
   -width=>4,
   -offvalue=>0,
   -onvalue=>1,
   -command=>\&sortby,
   )->pack(
      -side=>'left',
      -expand=>0,
      -padx=>0,
      -pady=>$ypad,
      -fill=>'y',
      );     

#frame for spacing 
$sortframe->Frame(
   -borderwidth=>'0',
   -width=>2,
   )->pack(
      -side=>'right',
      -padx=>0,
      -pady=>0,
      -expand=>0,
      );
      
#frame for spacing
$buttonframe->Frame(
   -borderwidth=>'0',
   -width=>2,
   )->pack(
      -side=>'left',
      -padx=>0,
      -pady=>0,
      -expand=>0,
      );
  
$buttonframe->Button(
   -text=>'Exit',
   -width=>$buttonwidth,
   -command=>\&save_exit,
   )->pack(
      -side=>'right',
      -padx=>0,
      -pady=>2,
      );

$buttonframe->Button(
   -text=>'Search',
   -width=>$buttonwidth,
   -command=>\&searchit,
   )->pack(
      -side=>'right',
      -padx=>1,
      -pady=>2,
      );
        
$printbutton=$buttonframe->Button(
   -text=>'Print',
   -width=>$buttonwidth,
   -command=>\&printit,
   )->pack(
      -side=>'right',
      -padx=>0,
      -pady=>2,
      );

$savebutton=$buttonframe->Button(
   -text=>'Save',
   -width=>$buttonwidth,
   -command=>sub{&savit("");},
   )->pack(
      -side=>'right',
      -padx=>1,
      -pady=>2,
      );

$typesbutton=$buttonframe->Button(
   -text=>'Clone',
   -width=>$buttonwidth,
   -command=>\&clone_data,
   )->pack(
      -side=>'right',
      -padx=>0,
      -pady=>2,
      );

#frame for which to stick the menubutton.  Menubuttons dont line up right with a 
#row of buttons so I have to put them into a frame and pad with another empty frame  :-\
$mbframe=$buttonframe->Frame( 
   )->pack(
      -side=>'right',  
      -padx=>0,
      -pady=>2,
      -expand=>0,
      -fill=>'y',
      );
    
$mbutton=$mbframe->Menubutton(
   -text=>' Snap',
   -width=>$buttonwidth-1,
   -relief=>'raised',
   -indicatoron=>1,
   )->pack(
      -side=>'right',
      -padx=>0,
      -pady=>1,
      -fill=>'y',
      );

$mbutton->command(
   -label=>'Take Snapshot 1',
   -command=>sub{&take_snapshot("1");},
   );
$mbutton->command(
   -label=>'Take Snapshot 2',
   -command=>sub{&take_snapshot("2");},
   );
$mbutton->command(
   -label=>'Take Snapshot 3',
   -command=>sub{&take_snapshot("3");},
   );
$mbutton->command(
   -label=>'Take Snapshot 4',
   -command=>sub{&take_snapshot("4");},
   );
       
$querybutton=$buttonframe->Button(
   -text=>'Exec',
   -width=>$buttonwidth,
   -foreground=>'red4',
   -command=>\&check_cmd,
   )->pack(
      -side=>'right',
      -padx=>0,
      -pady=>2,
      );

#this is important to do initially otherwise the histories wont be checkpointed
$dbserventry->invoke;
$dbuserentry->invoke;
$dbpassentry->invoke;

$qsentry1->invoke;
$qsentry2->invoke;
$qsentry3->invoke;

$qscheck1->update;
$qscheck2->update;
$qscheck3->update;

&act_deactivate("qsentry1","qsactive1");
&act_deactivate("qsentry2","qsactive2");
&act_deactivate("qsentry3","qsactive3");

#record the pack info for header and the data listboxes..
#needed when switching between command mode and query mode
@headerinfo=$queryheader->packInfo;
@datainfo=$queryout->packInfo;

#ensure default is on the list of dbusehist
$founddefault=grep(/^default/,@dbusehist);
if ($founddefault lt "1") {
   push (@dbusehist,"default");
   $dbuseentry->history([@dbusehist]);
   }
$dbuseentry->invoke;  

$tscrollx=0.0;
$tscrolly=0.0;

#force the optionmenu to be invoked, otherwise the first query will be sorted twice
$sortby="     ";
$sortbyentry->configure(-textvariable=>\$sortby);


MainLoop();

#                                         subroutines     
#------------------------------------------------------------------------------------------

sub clone_data {
   $CW->destroy if Exists($CW);
   $clonedate=$LW->cget(-title);
   #collect the x scroll setting so it can be set to the same as the real data window
   ($clscrollx,$rest)=$queryout->xview;
   ($clscrolly,$rest)=$queryout->yview;
   #The main clone window
   $CW=new MainWindow(-title=>"Cloned Data - $clonedate");
   #set a minimum size so the window cant be resized down to mess up the cancel button
   $CW->minsize(854,214);
   #The top frame for the text
   $cloneframe1=$CW->Frame(
      -borderwidth=>'0',
      -relief=>'flat',
      -background=>$background,
      )->pack(
         -expand=>1,
         -fill=>'both',
         );

   #frame for the buttons
   $cloneframe2=$CW->Frame(
      -borderwidth=>'0',
      -relief=>'flat',
      -background=>$background,
      -height=>60,
      )->pack(
         -fill=>'x',
         -expand=>0,
         );

   # Create a scrollbar on the right side and bottom of the text
   $hscrolly=$cloneframe1->Scrollbar(
      -orient=>'vert',
      -elementborderwidth=>1,
      -highlightthickness=>0,
      -background=>$background,
      -troughcolor=>$troughbackground,
      -relief=>'flat',
      )->pack(
         -side=>'right',
         -fill =>'y',
         );

   $hscrollx=$cloneframe1->Scrollbar(
      -orient=>'horiz',
      -elementborderwidth=>1,
      -highlightthickness=>0,
      -background=>$background,
      -troughcolor=>$troughbackground,
      -relief=>'flat',
      )->pack(
         -side=>'bottom',
         -fill=>'x',
         );
         
   $cloneheader=$cloneframe1->Text(
      -font=>$winfont,
      -xscrollcommand=>['set', $hscrollx],
      -relief=>'flat',
      -highlightthickness=>0,
      -background=>$headerbackground,
      -foreground=>$headerforeground,
      -selectforeground=>$txtforeground,
      -selectbackground=>'#c0d0c0',
      -wrap=>'none',  
      -height=>2,
      -width=>102,
      )->pack(
         -fill=>'x',
         -expand=>0,
         -pady=>0,
         -anchor=>'n',
         );
         
   $clonewin=$cloneframe1->Text(
      -yscrollcommand => ['set', $hscrolly],
      -xscrollcommand => ['set', $hscrollx],
      -font=>$winfont,
      -relief => 'sunken',
      -highlightthickness=>0,
      -foreground=>$txtforeground,
      -background=>$txtbackground,
      -borderwidth=>1, 
      -wrap=>'none',
      -height=>10,
      -width=>102,
      -exportselection=>1,
      )->pack(
         -expand=>1,
         -fill=>'both',
         );

   $hscrolly->configure(-command => ['yview', $clonewin]);
   $hscrollx->configure(-command=>\&my_clonexscroll);

   $cloneframe2->Label(
      -textvariable=>\$clonestat,
      -borderwidth=>1,
      -background=>$txtbackground,
      -foreground=>$rowcolcolor,
      -font=>$winfont,
      -relief=>'sunken'
      )->pack(
         -side=>'left',
         -padx=>3,
         -pady=>3,
         -fill=>'both',
         );

   $cloneframe2->Button(
      -text=>'Cancel',
      -borderwidth=>1,
      -width=>5,
      -background=>$buttonbackground,
      -foreground=>$txtforeground,
      -highlightthickness=>0,
      -font=>$winfont,
      -command=>sub{$CW->destroy;}
      )->pack(
         -expand=>0,
         -side=>'right',
         -padx=>0,
         -pady=>2,
         );
         
   $clonesavebutton=$cloneframe2->Button(
      -text=>'Save',
      -borderwidth=>1,
      -width=>5,
      -background=>$buttonbackground,
      -foreground=>$txtforeground,
      -highlightthickness=>0,
      -font=>$winfont,
      -command=>sub{&clone_savit("");},
      )->pack(
         -expand=>0,
         -side=>'right',
         -padx=>1,
         -pady=>2,
         );

  $cldbcmd=$cloneframe2->Menubutton(
      -text=>'Cmd',
      -relief=>'raised',
      -indicatoron=>0,
      -borderwidth=>1,
      -background=>$buttonbackground,
      -highlightthickness=>0,
      -width=>7,
      -tearoff=>0,
      -font=>$winfont,
      )->pack(
         -side=>'right',
         -padx=>0,
         -pady=>2,
         -fill=>'y',
         );

   #if there has been more than one resultcount returned, dont display the header 
   #$testhdata=$queryheader->get('0.0','end');
   @theaderdata=$queryheader->get('0.0','end');
   if ($resultcount==1) {
      #ensure there are no trailing spaces on the header to mess up the alignment with the data
      foreach (@theaderdata) {
         $_=~s/ +\n +/\n/g;
         }
      $cloneheader->insert('end',@theaderdata);
      }
   $cloneheader->tag('add','clonedbtype',"2.0","2.0 + 1 line");
   $cloneheader->tag('configure','clonedbtype',
      -foreground=>$datatypeforeground,
      ); 
   if ($resultcount>1||@theaderdata[0]!~/\w/) {            $cloneheader->packForget;
      $cloneheader->packForget;
      };
   @tquerydata=$queryout->get('0.0','end');
   $clonewin->insert('end',@tquerydata);
   #generate the status string for the clone window
   $clonestat=" Rows: $dbrowcount   Cols: $dbcolcount   Server: $dbserver  Database: $dbuse  MaxRows: $maxrowcount ";
   $savsqlstring=~s/^ +//;
   $savsqlstring=~s/ +$//;
   $cldbcmd->command(
      -label=>"$savsqlstring",
      -background=>$txtbackground,
      -activeforeground=>$txtforeground,
      -activebackground=>$txtbackground,
      );
   #scroll the window to display the same lines as the original window
   $cloneheader->xview(moveto=>$clscrollx);
   $clonewin->xview(moveto=>$clscrollx);
   $clonewin->yview(moveto=>$clscrolly);
}#sub clone
   
#tie two text widgets (header and data) to scroll horizontally together
sub my_xscroll {
   $queryheader->xview(@_); 
   $queryout->xview(@_);     
   }#sub

#tie two text widgets (header and data) to scroll horizontally together
sub my_clonexscroll {
   $cloneheader->xview(@_); 
   $clonewin->xview(@_);     
   }#sub

sub operconfirm {
   if ($dangerflag==1) {
      local $ask=$LW->messageBox(
         -icon=>'warning', 
         -type=>'OKCancel',
         -bg=>$background,
         -title=>'Action Confirm',
         -text=>"You are about to perform a potentially dangerous command on\n$dbserver!\n\nPlease confirm the action before\nit is executed..",
         -font=>'8x13bold',
         );
      return $ask;
      }else{
         return "Ok";
         }
}#sub operconfirm

#connect with the server and execute the proper command
sub check_cmd {
   #collect the x scroll setting so it can be resumed after the sort
   ($tscrollx,$rest)=$queryout->xview;
   ($tscrolly,$rest)=$queryout->yview;
   $dbserventry->invoke;
   $dbuserentry->invoke;
   $dbpassentry->invoke;
   $dbuseentry->invoke;
   $qsentry1->invoke;
   $qsentry2->invoke;
   $qsentry3->invoke;
   $dangerflag=0;	
   #start the command clean
   $sqlstring="";
   @dbretrows=();
   $confirm="";
   #set the newsearch flag to ensure any searching of the dbdata is restarted from the start since
   #new data will be generated..
   $newsearch=1;
   #force the query button to a normal state before the display is locked
   $querybutton->configure(-state =>'normal');
   $LW->update;
   #build the sql command string... to be used by the server and the isql binary too
   foreach ("querystring1","querystring2","querystring3") {
      #check to see which of the sql strings is enabled with the checkbutton - 
      #only collect and concatenate the enabled sql string lines
      $qsmark=substr($_,-1);
      $qsmark="qsactive$qsmark";
      if (${$qsmark}==1) {
         ${$_}=~s/^ *//;
         $sqlstring.="${$_} ";
         #get the first word of the sql string to check against the dangercmds list
         $verb=(split(/ +\w/,${$_}))[0];
         #check to see if the command is one of the dangerous ones to enable the confirmation when executed
         if (grep(/^$verb$/i,@dangercmds)) {
            $dangerflag=1;
            }
         }#if qsmark eq 1 
      }#foreach query string
   return if ($sqlstring=~/^ *$/);
   &setbusy;
   $confirm=&operconfirm;
   if ($confirm eq "Ok") {
      $date=`date`;
      $LW->configure(-title=>"DBGUI $VERSION  [$checkpointfile]  $date"); 
      #save off a wrapped version of the sqlstring for the ascii save files
      $savsqlstring=wrap("    ","    ","$sqlstring");
      #the header has to be nulled out for querys and db commands
      $queryheader->delete('0.0','end');
      $queryout->delete('0.0','end');
      $LW->update;
      #if the menuitem on the display is set to Isql or sqsh, call the isql binary for the
      #dbcommand and skip all of the other stuff
      if ($method eq "Isql"||$method eq "Sqsh") {
         &run_isql_cmd;
         &setunbusy;
         return;
         }
      &run_query;
      }#if confirm eq OK
   &setunbusy;
}#sub check_cmd

#sub to actually execute a DB query. the run_command routine execs all other DB commands
#with the messagehandler, there is no need to check each command for successful status
sub run_query {
   #connect to the database and run the command
   $dbh=DBI->connect("dbi:$servertype:server=$dbserver;logintimeout=60;timeout=240",$dbuser,$dbpass);
   #if the login info is bad, complain and quit.  The error handler posts the errors returned
   #from the libraries.  No need to add to them
   if (!$dbh) {
      $queryout->insert('end',"\n Open Connection to Database Server Failed..\n\n");
      return;
      }#if !dbh
   $dbh->{$errorhandler}=\&err_handler;
   if (int($maxrowcount)>0) {
      $status=$dbh->do("set rowcount $maxrowcount");
      if ($status==0) {
         $queryout->insert('end',"\n Set Rowcount Statement Failed..\n\n");
         return;
         }#if status eq 0
      }#if ($maxrowcount=~/\d+/) {
   #if the dbuse variable is not set to default, specifically set it.
   if ($dbuse !~ /default/i) {
      $status=$dbh->do("use $dbuse"); 
      if ($status==0) {
         return(1);
         }#if status eq 0
      }#if dbuse is not default
   $resultcount=0;
   @sortbyhist=();
   $skipsort=0;

   $sth=$dbh->prepare($sqlstring);
   $sth->execute;
   #if an error occured, the error handler will post the error text to the user, All that needs to be
   #done here is to return.
   if ($sth->err) {
      return 1;
      }
   #loop to execute for *each* result set returned
   do {
      $spstat=$sth->{$resulttypes};
      #if no status is returned , dont attempt to parse the results..  
      #This happens when a db command is executed that returns
      #no data - like truncate etc..
      if (!$spstat) {
         return(0);
         }
      $colnames=$sth->{NAME};
      $colsizes=$sth->{PRECISION};      
      $coltypes=$sth->{$dbtypes};
      
      ################################## Build the header ###################################  
      #get the number of columns
      $headerstring="";
      $colheaderstring="";
      $collengthheaderstring="";
      $divider="";
      for($i=0;$i<=$#$colnames;++$i) {
         #get the name of each column
         $colheader=@$colnames[$i];
         #get the data type for the column
         $coltype=@$coltypes[$i];
         $dispcoltype=$dbdatatypes{$coltype};
         #push the column name onto the sortby popup
         push(@sortbyhist,$colheader);
         #collect the length of the column header string
         $hlength{$i}=length($colheader);
         #get the length of the column data
         $sybcollength{$i}=@$colsizes[$i];

         #take the longest of the two column lengths for a good display
         if ($hlength{$i} > $sybcollength{$i}) { 
            $finalcollength{$i}=$hlength{$i}
            }else{
               $finalcollength{$i}=$sybcollength{$i};
               }
         
         #if a length value is found on the specialcollengths, use it *only* if it is bigger
         #than the finalcollength
         $testcollength=$specialcollengths{$coltype};
         if ($testcollength>$finalcollength{$i}) {
             $finalcollength{$i}=$testcollength;
             }
            
         #set a minimum of seven characters wide to handle the minimal col type/length row
         if ($finalcollength{$i}<7) {
            $finalcollength{$i}=7;
            }         
                        
         #pad the colheader with spaces to the final length   
         until ($hlength{$i} >= $finalcollength{$i}) {
            $colheader.=" ";
            $hlength{$i}++;
            }    

         #create the divider line..
         for($lc=1; $lc<=$finalcollength{$i}; ++$lc) { 
            $divider.="\-";
            }

         #tack on a delimiter for sorting
         $colheaderstring.="$colheader | ";
         $divider.=" | ";
         #build a string displaying the lengths of the columns 
         $collengthheader="$dispcoltype $sybcollength{$i}";
         #calculate the length of the real returned value of the length of the column
         $realhlength=length($collengthheader);
         #pad the string with spaces out to the column length          
         until ($realhlength >= $finalcollength{$i}) {
            $collengthheader.=" ";
            $realhlength++;
            }   

         #tack on the same delimiter as the data - for a nice display of columns
         $collengthheaderstring.="$collengthheader | ";
         }#for ($i=0;$i<=$dbcolcount;++$i) {

         #these strings are used later on to remove the first three lines of the returned data
         #if only one resultset is returned.  If any changes are made to these three elements,
         #the changes will also have to be detected in the upcoming command line like this:
         #until ($dbretrows[0]!~/^\n\Q$colheaderstring\E$|^\Q$collengthheaderstring\E$|^\Q$divider\E|^$/||!$dbretrows[0]) {
            push(@dbretrows,"\n");
            push(@dbretrows,"$colheaderstring");
            push(@dbretrows,"$collengthheaderstring");
            push(@dbretrows,"$divider");
         
          ################################## pull in the data ###################################
          #for each row returned from the query..
          while($dbdata=$sth->fetch) {
             #Pull together the data returned for sorting and display  
             $dbrowstring="";
             $i=0; 
             #dont use foreach here to ensure the data is in proper order
             for($xx=0; $xx<scalar(@$dbdata); ++$xx) { 
                #calculate the length of the real returned data 
                $element="@$dbdata[$xx]";

                #pad the string with spaces out to the column length
                until (length($element) >= $finalcollength{$i}) {
                   $element.=" ";
                   }#until
                #tack on a delimiter for sorting
                $dbrowstring.="$element | ";
                $i++;
                }#foreach @dbdata
             push(@dbretrows,"$dbrowstring");
             }#while ($d=$sth->fetch)    
          $resultcount++;
      }while($sth->{syb_more_results});
   #4043 is the status from the server for the sql command.  It is returned as a separate result
   #set.  If it is detected, chop the data out of the final data and remove the column from the 
   #sort history
   if ($spstat==4043) {
      splice(@dbretrows,-4,4);
      splice(@sortbyhist,-1,1);
      $resultcount--;
      }
      
   #if only one resultset has been returned, populate and display the pretty header
   #otherwise display the plain db text
   if ($resultcount==1 && $skipsort==0) {
      $queryheader->delete('0.0','end');
      #if the first element is empty remove it
      if ($dbretrows[0] eq "") {
         splice(@dbretrows,0,1);
         }
      #take off the first few elements of the retrows array until real data is encountered
      #or until there is no data on the array at all (like when a truncate command etc is executed)
      until ($dbretrows[0]=~/^\w+/||!$dbretrows[0]) {
         splice(@dbretrows,0,1);
         }
      #move the header info from the dbretrows array into the queryheader textbox
      #the header and data have to be repacked in order, otherwise they get flipped
      $queryheader->insert('end',"$dbretrows[0]\n");
      $queryheader->insert('end',"$dbretrows[1]");
      splice(@dbretrows,0,3);
      #set query state so sorts etc are allowed   
      }#if ($resultcount==1 && $skipsort==0)
   &sortby;
   }#sub run_query

#connect with server and execute a DB command using the isql or sqsh binary
sub run_isql_cmd {
   $queryheader->packForget;
   &set_command_state;
   $usecmd="";
   #if the maxrowcount is 0, dont set one
   if ($maxrowcount>0) {
      $usecmd="set rowcount $maxrowcount\ngo";
      }
   #if the database field is not default, set it   
   if ($dbuse !~ /default/i) {
      $usecmd.="\nuse $dbuse\ngo";
      }
   if ($method eq "Isql") {   
      $sqlbinary=$isqlbinary;
      }
   if ($method eq "Sqsh") {   
      $sqlbinary=$sqshbinary;
      }
   @dbretrows=`$sqlbinary -U$dbuser -P$dbpass -S$dbserver -w999 <<EOD\n$usecmd\n$sqlstring\ngo\nEOD`;
   $queryout->insert('end',"\ @dbretrows"); 
   }#sub

#set the busy LED to red  
sub setbusy {
   $busymarker->configure(-background=>$busycolor);
   #$busymarker->itemconfigure('circle',-fill=>$busycolor,-outline=>'black');
   $LW->update;
   }

#return the busy LED to green
sub setunbusy {
   $busymarker->configure(-background=>$unbusycolor);
   #$busymarker->itemconfigure('circle',-fill=>$unbusycolor,-outline=>'grey40');
   $LW->update;
   }  

#configure colors to make these labels and the sort checkboxes available
sub set_query_state {
   $queryheader->pack(@headerinfo);
   $queryout->pack(@datainfo);
   #manually set the history for sortby and move the display back to where it was previously, also
   #make sure the width is set, otherwise, the menubutton will resize and mess up the execute button
   $sortbyentry->configure(-options=>\@sortbyhist,-width=>24,-justify=>'left',-state=>'normal');
   $sortlabel->configure(-foreground=>$txtforeground);
   $colnumlabel->configure(-foreground=>$txtforeground);
   $rownumlabel->configure(-foreground=>$txtforeground);  
   $revsortbutton->configure(-state=>'normal',-selectcolor=>'red4');
   $numsortbutton->configure(-state=>'normal',-selectcolor=>'red4');
   $queryheader->tag('add','dbtype',"2.0","2.0 + 1 line");
   $queryheader->tag('configure','dbtype',
      -foreground=>$datatypeforeground,
      );   
   }

#configure colors to make these labels and the sort checkboxes unavailable
sub set_command_state {
   $queryheader->packForget;
   $queryout->pack(@datainfo);
   $sortby=" ";
   $sortlabel->configure(-foreground=>'grey65');
   $revsortbutton->configure(-state=>'disabled',-selectcolor=>$buttonbackground);
   $numsortbutton->configure(-state=>'disabled',-selectcolor=>$buttonbackground);
   $sortbyentry->configure(-state=>'disabled');
   $colnumlabel->configure(-foreground=>'grey65');
   $rownumlabel->configure(-foreground=>'grey65');   
   @sortbyhist=();
   $dbrowcount="";
   $dbcolcount="";
   }

#the sort routine can be called standalone, so it is splitout of the run_query routine
sub sortby {
   #execute the sort ONLY if 1 result set has been returned and the skipsort flag is 0
   if ($resultcount==1 && $skipsort==0) { 
      #detect whether the scrollbars have moved since the db command was executed.  If so,
      #use the current positions, otherwise use the original ones from the check_cmd subroutine
      ($sortscrollx,$rest)=$queryout->xview;
      if ($tscrollx ne $sortscrollx&&$sortscrollx>0) {
         $tscrollx=$sortscrollx;
         }
      ($sortscrolly,$rest)=$queryout->yview;
      if ($tscrollY ne $sortscrolly&&$sortscrolly>0) {
         $tscrolly=$sortscrolly;
         }
      if ($sortby=~/^ *$/) {
         $sortby=$sortbyhist[0];
         }
      if (grep(/^\Q$sortby\E$/,@sortbyhist)) {
         # we have to figure what element of the sortbyhist array the sort parameter is..
         $sortindex=0;
         foreach (@sortbyhist){
            $sortindex++;
            #if we find the sort parameter in the sortbyhist array, exit the loop
            last if (/^\Q$sortby\E$/);
            }#foreach @sortbyhist
         }else{
            $sortindex=0;
            $sortby=();
            }#else if grep sortby..
      #if the numeric flag is set, sort differently
      if ($numsort) {
         $sortindex.="n";
         }
      #if the reverse flag is set, sort differently again
      if ($reversesort) {
         $sortindex="\-$sortindex";
         }
      #dont really execute the sort unless the sortby variable is set.  This is to keep
      #from double sorting.  Once when sortby is called and again when the sortbyentry
      #optionmenu is configured with the sort items     
      if ($sortby) {
         #execute the sort 
         @dbretrows=fieldsort '\|',[$sortindex],@dbretrows;
         #remove the first element if it is an empty line from the sort
         if ($dbretrows[0] =~/^ *$/) {
            splice(@dbretrows,0,1);
            }
         }#if sortby
      }#if resultcount ==1
   #clear out the queryout text widget and replace with the sorted rows
   $queryout->delete('0.0','end');
   $dbrowcount=0;
   #post the results regardless of whether or not a sort is being executed
   for ($t=0; $t<scalar(@dbretrows); $t++) {
      if ($dbretrows[$t] ne "") {
         #remove any accidental tabs found in the data and replace with a single space
         #since I calculate the widths of the columns by the number of characters, tabs
         #only get counted as a single character.  It is safe to remove them and replace with
         #a single space without worrying about mis-aligned columns
         $dbretrows[$t]=~s/\t/ /g;
         $dbrowcount++;
         $queryout->insert('end',"$dbretrows[$t]\n");
         }#if dbretrows
      }#for ($t=0; $t<scalar(@dbretrows); $t++)
   #check the header to see if it contains any real data.  This is for thos sp_commands that only
   #return one resultset, but dont have a  structured table style output, therefore we need to treat
   #the data like a command not a table.   ex - sp_lock
   $testhdata=$queryheader->get('0.0','end');
   #if only one result was returned set the query state, otherwise set the command state
   if ($resultcount==1&&$testhdata=~/\w/) {
      #it is easier and more accurate to get the final row and column counts from the actual
      #data being displayed. 
      $dbcolcount=-1;
      foreach (split(/\|/,"$dbretrows[0]")) {
         $dbcolcount++;
         }
      &set_query_state;
      }else{
         &set_command_state
         }
   $queryheader->xview(moveto=>$tscrollx);
   $queryout->xview(moveto=>$tscrollx);
   $queryout->yview(moveto=>$tscrolly);
   $queryout->update;
   }#sub sortby

#write out the returned query information to an ascii file 
sub savit {
   ($outfile)=@_;
   if ($outfile eq "") {
      $savebutton->configure(-state=>'normal');
      @types =
      (["Log files ",          ['.out']],
       ["Text files",          ['.txt']],
       ["All files ",          ['*']],
      ); 
   $LW->optionAdd("*background","$savedialogcolor"); 
   $LW->optionAdd("*highlightBackground", "$savedialogcolor");
   $outfile=$LW->getSaveFile(
      -filetypes        => \@types,
      -initialfile      => 'dbgui.out',
      -defaultextension => '.out',
      );
   $LW->optionAdd("*background","$background"); 
   $LW->optionAdd("*highlightBackground", "$savedialogcolor");
   #if the save dialog was canceled off, dont continue
   return if ($outfile eq "");
   }
   $date=`date`;
   open(outfile, ">$outfile") || die "Can't open save file :$outfile";
   print outfile "\nReport created $date";
   print outfile "Query Data:";
   print outfile "  Server Name - $dbserver";  
   print outfile "     Username - $dbuser";
   print outfile "Database Name - $dbuse";
   if ($maxrowcount) {
      print outfile "Max Row Count - $maxrowcount";
      }
   foreach ("querystring1","querystring2","querystring3") {
      #check to see which of the sql strings is enabled with the checkbutton
      #only print the enabled ones
      $qsmark=substr($_,-1);
      $qsmark="qsactive$qsmark";
      if (${$qsmark}==1) {
         print outfile " Query String - ${$_}";
         }
      }#foreach
   print outfile "Rows Returned - $dbrowcount";
   print outfile "Cols Returned - $dbcolcount\n";
   print outfile "Returned Data:\n";
   $queryhsave=$queryheader->get('0.0','end');
   $querydsave=$queryout->get('0.0','end');
   $queryhsave=~s/\n+$//;
   chomp $querydsave;
   print outfile "$queryhsave";
   #create a divider line to go in the output report between the header and data lines
   $thsave=$queryheader->get('0.0','2.1');
   $divider="";
   for($i = 1; $i < (length($thsave)-2); ++$i) {
      $divider.="-";
      }
   print outfile "$divider";   
   print outfile "$querydsave";
   close outfile;
   }#sub savit


#write out the clone window data to an ascii file 
sub clone_savit {
   ($cloneoutfile)=@_;
   if ($cloneoutfile eq "") {
      $clonesavebutton->configure(-state=>'normal');
      @types =
      (["Log files ",          ['.out']],
       ["Text files",          ['.txt']],
       ["All files ",          ['*']],
      ); 
   $LW->optionAdd("*background","$savedialogcolor"); 
   $LW->optionAdd("*highlightBackground", "$savedialogcolor");
   $cloneoutfile=$LW->getSaveFile(
      -filetypes        => \@types,
      -initialfile      => 'clone_dbgui.out',
      -defaultextension => '.out',
      );
   $LW->optionAdd("*background","$background"); 
   $LW->optionAdd("*highlightBackground", "$savedialogcolor");
   #if the save dialog was canceled off, dont continue
   return if ($cloneoutfile eq "");
   }
   $date=`date`;
   open(outfile, ">$cloneoutfile") || die "Can't open save file :$cloneoutfile";
   print  outfile "\nCloned Data Report created $date\n\nQuery Data:";
   print outfile "$clonestat\n";
   local $mytempcmd=$cldbcmd->entrycget('end',-label);
   print outfile " DBCmd - $mytempcmd"; 
   print outfile "\nReturned Data:\n";  
   $clqueryhsave=$cloneheader->get('0.0','end');
   $clqueryhsave=~s/\n+$//;
   chomp $clquerydsave;
   print outfile "$clqueryhsave";
   #create a divider line to go in the output report between the header and data lines
   $clthsave=$cloneheader->get('0.0','2.1');
   $cldivider="";
   for($i = 1; $i<(length($clthsave)-2); ++$i) {
      $cldivider.="-";
      }
   print outfile "$cldivider";
   $clquerydsave=$clonewin->get('0.0','end');
   print outfile "$clquerydsave";
   close outfile;
   }#sub clone_savit

sub printit {
   &savit("/tmp/dbgui.prt"); 
   $p=$LW->PrintDialog(
      -Printers=>\@printers,
      -InFile=>$outfile,
      -Program=>$psprint,
      );
   $p->Show;
   $outfile="";
   }#sub printit

#eval the snapshot string for the current snapshot variable value
sub run_snapshot {
   ($snapnum)=@_;
   $tsnap="snapshot$snapnum";
   (eval $$tsnap);
   #once the snapshot string has been executed, pull the single quotes off of the query strings
   #otherwise, everytime a snapshot is executed, the slashes start stacking up, we dont want
   #the slashes displayed in the GUI, only in the checkpoint file
   foreach ($querystring1,$querystring2,$querystring3) {
      #replace any single quote strings with an escaped quote 
      $_ =~ s/\\'/\'/g;
       $_ =~ s/\\"/\"/g;
      $_ =~ s/\\@/\@/g;
      }
   &act_deactivate("qsentry1","qsactive1");
   &act_deactivate("qsentry2","qsactive2");
   &act_deactivate("qsentry3","qsactive3");
   }#sub run snapshot

#capture the snapshot string to be saved
sub take_snapshot {
   ($snapnum)=@_;
   $tsnap="snapshot$snapnum";
   foreach ($querystring1,$querystring2,$querystring3) {
      #replace any slashes with an escaped quote with a three slashes and a single quote
      #needed to properly save the values off in the .dbgui file 
      $_ =~ s/\\*\'/\\\'/g;
      #substitute double quotes for escaped ones
      $_=~s/\"/\\\"/g;    
      }
        
   #collect all other variables for the snapshot string
   $snapshotstring="";   
   foreach (@variablelist) {
      next if (/^snapshot/);
      $snapshotstring.="\$$_=\'$$_\'\;"
      }  
   ${$tsnap}=$snapshotstring;   
   &run_snapshot("$snapnum");
   }#sub snapshot

#save the checkpoint file and exit the program
sub save_exit { 
   #write out the checkpoint file for the next time the utility is started
   open(ckptfile, ">$checkpointfile") or die "Can't open checkpoint file - $checkpointfile"; 
   print ckptfile "\#Checkpoint file for dbgui.pl utility";
   print ckptfile "\#Query parameters and histories are saved on exit and restored on startup\n";
   print ckptfile "\#NOTE - Snapshot0 is used to set the variables on application startup, but";
   print ckptfile "\#the variables have to be initialized for the ComboEntries..  therefore they";
   print ckptfile "\#are set to null initially and redifined from Snapshot0..\n";

   #Snapshot 0 is always the state the utility was last left if exited properly.
   #Since snapshot 0 will be restored on startup, there is no need to record any variables
   #that are not the snapshot strings - however if the variables are not initialized,
   #the history arrays will get lost the next time the utility is started, so I write all
   #variables to the checkpoint file as empty even though they are redefined with snapshot0 
   &take_snapshot("0");
   
   #since the variables can contain dollar signs (like in sp_helptext commands) 
   #etc... escape the special characters
   foreach (@variablelist) {
      if (!/^snapshot/) {
         print ckptfile "\$$_=\"\"\;";
         }else{
            if ("${$_}" ne "") {      
               print ckptfile "\$$_=q\($$_\)\;";
               }else{
                   #the snapshot variable is empty - write out null definitions for each variable
                   $snapshotstring="$_\=q\(";   
                   foreach (@variablelist) {
                      next if (/^snapshot/);
                      $snapshotstring.="\$$_=\'\'\;"
                      }
                    ${$_}=$snapshotstring;
                    print ckptfile "\$${$_}\)\;";
                   }#else
             }#first else  
      }#foreach variablelist 
   foreach $arrayname (@arraylist) {
      $arraystring="\@$arrayname=(\n";
      foreach (@{$arrayname}) {
         #substitute double quotes for escaped ones
         $_=~s/\"/\\\"/g;          
         #substitute @ symbols for escaped ones
         $_=~s/\@/\\\@/g;         
         $arraystring.="\"$_\",\n";
         }
      $arraystring.="\);";  
      print ckptfile "\n$arraystring";
      }
   print ckptfile "\n1\;";
   close ckptfile;  
   exit;
   }#sub save_exit

#configure the query strings to be greyed or black depending on their execute state set
#by the checkbuttons
sub act_deactivate {
   ($querywid,$queryline)=@_;
   if (${$queryline} eq "1") {
      ${$querywid}->configure(-fg=>$txtforeground);
      ${$querywid}->focus;
      }else{
         ${$querywid}->configure(-fg=>'grey65');
         }
    ${$querywid}->update;
   }#sub

#error handler taken from subutil.pl in the sybperl distribution.  Needed to trap
#the error strings returned for non DB type
sub err_handler {
   my ($err, $severity, $state, $line, $server, $proc, $msg)= @_;
   #print "ERROR HANDLER\n($err, $severity, $state, $line, $server, $proc, $msg)";
   # Check the error code to see if we should report this.   
   if ($severity >10) {
      $msg=wrap(" "," ","$msg");
      $queryout->insert('end',"Error:$err\nProcedure:$proc\nLine:$line\nState:$state\nSeverity:$severity\n\n$msg");
      $skipsort=1;
      &set_command_state;
      return 1;
      }
   if ($err==0 && $msg !~/^ *$/) {
      return if ($msg =~/^Message empty/);
      push(@dbretrows,"$msg");
      $skipsort=1;
      return 0;
      }
}#sub error_handler

#query results search dialog
sub searchit {
   $srchstring="";
   $SW->destroy if Exists($SW);
   $SW=new MainWindow(-title=>'DBGUI search');

   #set some nice parameters to be inherited by the search histentry
   $SW->optionAdd("*background","$background");
   $SW->optionAdd("*frame*relief", "flat");
   $SW->optionAdd("*font", "8x13bold");
   
   #width,height in pixels    
   $SW->minsize(424,51);
   $SW->maxsize(724,51);

   #default to non case sensitive
   $caseflag="nocase";
   $newsearch=1;
   
   #The top frame for the text
   $searchframe1=$SW->Frame(
      -borderwidth=>'0',
      -relief=>'flat',
      -background=>$background,
      )->pack(
         -expand=>1,
         -fill=>'both',
         );

   $searchframe2=$SW->Frame(
      -borderwidth=>'0',
      -relief=>'flat',
      -background=>$background,
      )->pack(
         -fill=>'x',
         -pady=>2,
         );

   $searchframe1->Checkbutton(
      -variable=>\$caseflag,
      -font=>$winfont,
      -relief=>'flat',
      -text=>"Case",
      -highlightthickness=>0,
      -highlightcolor=>'black',
      -activebackground=>$background,
      -bg=>$background,
      -foreground=>$txtforeground,
      -borderwidth=>'1',
      -width=>6,
      -offvalue=>"nocase",
      -onvalue=>"case",
      -command=>sub{$current='0.0',$searchcount=0;$newsearch=1},
      -background=>$background,
      )->pack(
         -side=>'left',
         -expand=>0,
         );
         
   $searchhistframe=$searchframe1->Frame(
   -borderwidth=>1,
   -relief=>'sunken',
   -background=>$background,
   -foreground=>$txtforeground,
   -highlightthickness=>0,
   )->pack(
      -side=>'bottom',
      -expand=>0,
      -pady=>0,
      -padx=>1,
      -fill=>'x', 
      );
      
   $ssentry=$searchhistframe->HistEntry(
      -font=>$winfont,
      -relief=>'sunken',
      -textvariable=>\$srchstring,
      -highlightthickness=>0,
      -highlightcolor=>'black',
      -selectforeground=>$txtforeground,
      -selectbackground=>'#c0d0c0',
      -background=> 'white',
      -bg=>$background,
      -foreground=>$txtforeground,
      -borderwidth=>0,
      -bg=> 'white',
      -limit=>$histlimit,
      -dup=>0,
      -match => 1,  
      -justify=>'left',
      -command=>sub{@searchhist=$ssentry->history;},
      )->pack(
         -fill=>'both',
         -expand=>0,
         );

   #press enter and perform a single fine
   $ssentry->bind('<Return>'    => \&find_one);
   $ssentry->bind('<Up>'        => sub { $ssentry->historyUp });
   $ssentry->bind('<Control-p>' => sub { $ssentry->historyUp });
   $ssentry->bind('<Down>'      => sub { $ssentry->historyDown });
   $ssentry->bind('<Control-n>' => sub { $ssentry->historyDown });
   $ssentry->history([@searchhist]);

   $searchframe2->Button(
      -text=>'Find',
      -borderwidth=>'1',
      -width=>'10',
      -background=>$buttonbackground,
      -foreground=>$txtforeground,
      -highlightthickness=>0,
      -font=>$winfont,
      -command=>\&find_one,
      )->pack(
         -side=>'left',
         -padx=>2,
         );

   $searchframe2->Button(
      -text=>'Find All',
      -borderwidth=>'1',
      -width=>'10',
      -background=>$buttonbackground,
      -foreground=>$txtforeground,
      -highlightthickness=>0,
      -font=>$winfont,
      -command=>\&find_all,
      )->pack(
         -side=>'left',
         -padx=>2,
         );

   $searchframe2->Button(
      -text=>'Cancel',
      -borderwidth=>'1',
      -width=>'10',
      -background=>$buttonbackground,
      -foreground=>$txtforeground,
      -highlightthickness=>0,
      -font=>$winfont,
      -command=>sub{$SW->destroy;$queryout->tag('remove','search', qw/0.0 end/);}
      )->pack(
         -side=>'right',
         -padx=>2,
         );
   $ssentry->invoke;      
   $ssentry->focus;
} # sub search


# search the Logfile for a term and return a highlighted line containing the term.
sub find_all {
   return if ($srchstring eq "");
   $ssentry->invoke;
   #delete any old tags so new ones will show
   $queryout->tag('remove','search', qw/0.0 end/);
   $current='0.0';
   $stringlength=length($srchstring);
   $searchcount=0;
   while (1) {
      if ($caseflag eq "case") {  
         $current=$queryout->search(-exact,$srchstring,$current,'end');
         }else{
            $current=$queryout->search(-nocase,$srchstring,$current,'end');
            }#else  
      last if (!$current);
      $queryout->tag('add','search',$current,"$current + $stringlength char");
      $queryout->tag('configure','search',
         -background=>'chartreuse',
         -foreground=>'black',
         );
      $searchcount++;       
      $current=$queryout->index("$current + 1 char");
      }#while true
   $SW->configure(-title=>"$searchcount Matches");
   $searchcount=0;
   $current='0.0';
}#sub find all

#find and highlight one instance of a string at a time
sub find_one {
   return if ($srchstring eq "");
   $ssentry->invoke;
   $queryout->tag('remove','search', qw/0.0 end/);
   #mull through the text tagging the matched strings along the way
   if ($srchstring ne $srchstringold || $newsearch==1) {
      $allcount=0;
      $tempcurrent='0.0';
      $srchstringold=$srchstring;
      while (1) {
         if ($caseflag eq "case") {  
            $tempcurrent=$queryout->search(-exact,$srchstring,$tempcurrent,'end');
            }else{
               $tempcurrent=$queryout->search(-nocase,$srchstring,$tempcurrent,'end');
               }#else  
         last if (!$tempcurrent);
         $allcount++;       
         $tempcurrent=$queryout->index("$tempcurrent + 1 char");
         $searchcount=0;
         $current='0.0';
         }#while true
     $newsearch=0; 
    }#if srchstring ne srstringold
   #set the titlebar of the search dialog to indicate the matches
   $SW->configure(-title=>"$allcount Matches");  
   $stringlength=length($srchstring);
   if (!$current) {
      $current='0.0';
      $searchcount=0;
      } # if current
   local $currentold=$current;   
   if ($caseflag eq "case") {  
      $current=$queryout->search(-exact,$srchstring,"$current +1 char");
      }else{
         $current=$queryout->search(-nocase,$srchstring,"$current +1 char");
         }#else
   #no matches were found - set the titlebar
   if ($current eq "") {
      $SW->configure(-title=>"No Matches");
      return;
      }      
   $current=$queryout->index($current);
   $queryout->tag('add','search',$current,"$current + $stringlength char");
   $queryout->tag('configure','search',
      -background=>'chartreuse',
      -foreground=>'black',
      );         
   $queryout->see($current);
   #see where the display has horizontally scrolled and move the header text to match 
   ($tscrollx,$rest)=$queryout->xview;
   $queryheader->xview(moveto=>$tscrollx);
} #sub find one

#return a positive status 
1;
