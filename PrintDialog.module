##############################################################################
## Program: PrintDialog - a reusable Tk-Widget interface to genscript or 
## similar type ascii to Postscript print programs 
##
## Author: Al Dorrington, Delco Electronics, awdorrin@ictest.delcoelect.com
##
#### 
## Version 1.0 - Initial Release - 9Jun97 
##
## Copyright (c) 1997 Al Dorrington. All rights reserved. 
## This program is free software; you can redistribute it and/or modify 
##
## it under the terms of the GNU General Public License as published by 
## the Free Software Foundation. 
##
## This program is distributed in the hope that it will be useful, 
## but WITHOUT ANY WARRANTY; without even the implied warranty of 
## MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the 
## GNU General Public License for more details.
## You can receive a copy of the GNU General Public License by writing to 
## Free Software Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA. 
##
## If you do change this program, please mail a copy of the modified code to
## me at: awdorrin@ictest.delcoelect.com 
##
##############################################################################
package Tk::PrintDialog;
use strict;
require Tk::Toplevel;
use Tk::ROText;

@Tk::PrintDialog::ISA=qw (Tk::Toplevel);
Construct Tk::Widget 'PrintDialog';
$Tk::PrintDialog::VERSION='1.0';


##############################################################################
# Define all variables as global, I'll move the non-global ones later
##############################################################################
my $program;
my $copies=1;

my ( $prt_opt_f, $printer_f, $options_f, $filename_f, $buttons_f, $status_f, $options_f1, $options_f2 );
my ( $prt_om, $fontsize_om );
my ( $file_e, $copy_e, $copyarg );
my ( $cancel_b, $print_b);
my ($prt_l, $fontsize_l, $style_l, $copy_l, $file_l, $status_l, $status_t );
my ( $InFile, $OutFile, $RmFile, $Debug, $Status, $printer_set, $font_set, $size_set );
my ( $CkBtn1_cb, $CkBtn2_cb, $CkBtn3_cb, $CkBtn4_cb, $CkBtn5_cb );
my ( $CkBtn1_set, $CkBtn2_set, $CkBtn3_set, $CkBtn4_set, $CkBtn5_set );
my ( $CkBtn1_L, $CkBtn2_L, $CkBtn3_L, $CkBtn4_L, $CkBtn5_L );
my ( $Opt1, $Opt2, $Opt3, $Opt4, $Opt5 );
my ( $pad, $prt_f, $size_f, $psfile_f, $scrolly, $fnt_f); 

my $windowback="bisque3";
my $buttonback="bisque2";
my $menuwidth=14;
##############################################################################
sub Version { return $Tk::PrintDialog::VERSION; }
##############################################################################

sub Populate {
my($cw, @args)=@_;

$cw->SUPER::Populate(@args);

## Create the toplevel window
$cw->withdraw;
$cw->protocol('WM_DELETE_WINDOW'=>sub {});
$cw->transient($cw->toplevel);
$cw->minsize(355, 243);
$cw->maxsize(355, 243);
### Set up the status
$cw->{'Shown'}=0;

#############################################################################
### Create the dialog
#############################################################################
# Create Frames 

$prt_opt_f=$cw->Frame( 
  -relief=>'raised', 
  -borderwidth=>'1',
  -background=>$windowback,  
  );

$pad=$prt_opt_f->Frame( 
  -relief=>'flat', 
  -borderwidth=>'0',
  -background=>$windowback,
  -height=>5,  
  );

$printer_f=$prt_opt_f->Frame(
  -relief=>'flat', 
  -borderwidth=>'1',
  -background=>$windowback,  
  );

$options_f=$prt_opt_f->Frame(
  -relief=>'flat', 
  -borderwidth=>'1',
  -background=>$windowback,  
  );
  
$filename_f=$cw->Frame(
  -relief=>'flat', 
  -borderwidth=>'1',
  -background=>$windowback,  
  );
  
$buttons_f=$cw->Frame(
  -relief=>'raised', 
  -borderwidth=>'1',
  -background=>$windowback,  
  );
  
$status_f=$cw->Frame(
  -relief=>'flat', 
  -borderwidth=>'1',
  -background=>$windowback,  
  );

$pad->pack( 
  -side=>'top', 
  -fill=>'x', 
  -expand=>'no');


$prt_opt_f->pack( 
  -side=>'top', 
  -anchor=>'w', 
  -fill=>'both', 
  -expand=>'yes');

$printer_f->pack( 
  -side=>'left', 
  -anchor=>'w', 
  -fill=>'both', 
  -expand=>'yes');

$options_f->pack( 
  -side=>'left', 
  -anchor=>'w', 
  -fill=>'both',
  );

$filename_f->pack( 
  -side=>'top', 
  -anchor=>'w', 
  -fill=>'x', 
  -expand=>'no');
  
$buttons_f->pack( 
  -side=>'top', 
  -anchor=>'e', 
  -fill=>'both', 
  -expand=>'yes');

$status_f->pack( 
  -side=>'top', 
  -anchor=>'e', 
  -fill=>'both', 
  -expand=>'yes');

#############################################################################
# Create Printer, Font and Size Selection Frame Contents


$prt_f=$printer_f->Frame(
  -background=>$windowback,
  );

$prt_l=$prt_f->Label(
  -text=>"  Printer:",
  -background=>$windowback,
  -justify=>'right',
  );

$prt_om=$prt_f->Optionmenu(
  -underline=>0,
  -relief=>'raised',
  -textvariable=>\$printer_set,
  -highlightthickness=>0,
  -borderwidth=>1,
  -background=>$buttonback,
  -width=>$menuwidth,
  -command=>sub{&checkprinter},
  );

$size_f=$printer_f->Frame(
  -background=>$windowback,
  );  
  
$fontsize_l=$size_f->Label(
  -text=>"Font Size:",
  -background=>$windowback,  
  -justify=>'right',
  );

$fontsize_om=$size_f->Optionmenu(
  -underline=>0,
  -relief=>'raised',
  -textvariable=>\$size_set,
  -highlightthickness=>0,
  -borderwidth=>1,
  -background=>$buttonback,
  -width=>$menuwidth,  
  );

# Create Filename Entry Frame Contents
$psfile_f=$printer_f->Frame(
  -background=>$windowback,
  -borderwidth=>0,
  -relief=>'flat',
  );
  
$file_l=$psfile_f->Label( 
  -text=>"  Outfile:",
  -highlightthickness=>0,
  -borderwidth=>1,
  -background=>$windowback,
  );

$file_e=$psfile_f->Entry(
  -textvariable=>\$OutFile,
  -highlightthickness=>0,
  -borderwidth=>2,
  -background=>'white', 
  -width=>$menuwidth+5,  
  -relief=>'sunken',
  );

$prt_f->pack( -side=>'top');
$prt_l->pack( -side=>'left',-pady=>2);
$prt_om->pack(-side=>'left',-padx=>'5' ,-pady=>2);

$size_f->pack( -side=>'top');
$fontsize_l->pack( -side=>'left',-pady=>2);
$fontsize_om->pack(-side=>'left',-padx=>'5' ,-pady=>2);

$psfile_f->pack( -side=>'top',-pady=>2);
$file_l->pack( -side=>'left');
$file_e->pack(-side=>'left',-padx=>'5');


#############################################################################
# Create Copies and Options Selection Frame Contents

# Need some sub Frames first
$options_f1=$options_f->Frame(  
  -background=>$windowback,
  );
$options_f2=$options_f->Frame(  
  -background=>$windowback,
  );

$options_f1->pack( -side=>'top', -anchor=>'w', -fill=>'both');
$options_f2->pack( -side=>'top', -anchor=>'w', -fill=>'both');

# Start the contruction
$copy_l=$options_f1->Label(
  -text=>"Copies:",
  -highlightthickness=>0,
  -borderwidth=>1,
  -background=>$windowback,
  );
$copy_e=$options_f1->Entry(
  -textvariable=>\$copies,
  -highlightthickness=>0,
  -borderwidth=>1,
  -background=>'white',
  -width=>3,
  );

$style_l=$options_f2->Frame(
  -background=>$windowback,
  -height=>3,
  );

$CkBtn1_cb=$options_f2->Checkbutton(
  -background=>$windowback,
  -relief=>'flat',
  -highlightthickness=>0,
  -borderwidth=>1,
  -variable=>\$CkBtn1_set);
  
$CkBtn2_cb=$options_f2->Checkbutton(
  -background=>$windowback,
  -relief=>'flat',
  -highlightthickness=>0,
  -borderwidth=>1,
  -variable=>\$CkBtn2_set);
$CkBtn3_cb=$options_f2->Checkbutton(
  -background=>$windowback,
  -relief=>'flat',
  -highlightthickness=>0,
  -borderwidth=>1,
  -variable=>\$CkBtn3_set);
$CkBtn4_cb=$options_f2->Checkbutton(
  -background=>$windowback,
  -relief=>'flat',
  -highlightthickness=>0,
  -borderwidth=>1,
  -variable=>\$CkBtn4_set);
$CkBtn5_cb=$options_f2->Checkbutton(
  -background=>$windowback,
  -relief=>'flat',
  -highlightthickness=>0,
  -borderwidth=>1,
  -variable=>\$CkBtn5_set);

$copy_l->pack(-side=>'left'); 
$copy_e->pack(-side=>'left');
$style_l->pack(-side=>'top', -anchor=>'w');
$CkBtn1_cb->pack(-side=>'top', -fill=>'x', -expand=>'yes');
$CkBtn2_cb->pack(-side=>'top', -fill=>'x', -expand=>'yes');
$CkBtn3_cb->pack(-side=>'top', -fill=>'x', -expand=>'yes');
$CkBtn4_cb->pack(-side=>'top', -fill=>'x', -expand=>'yes');
$CkBtn5_cb->pack(-side=>'top', -fill=>'x', -expand=>'yes');


#############################################################################
# Create Button Frame Contents

$print_b=$buttons_f->Button(
  -background=>$buttonback,
  -text=>'Print',
  -borderwidth=>1,
  -highlightthickness=>0,  
  -command=>sub { &Do_Print } );
  
$cancel_b=$buttons_f->Button(
  -background=>$buttonback,
  -text=>'Cancel',
  -borderwidth=>1,   
  -highlightthickness=>0,
  -command=>sub { $cw->unShow; } );

my $def_btn=$buttons_f->Frame(
  -relief=>'sunken',
  -borderwidth=>1,
  -background=>$windowback,
  );
$print_b->raise($def_btn);
$def_btn->pack(-side=>'left', -expand=>1);
$print_b->pack( -in=>$def_btn, -padx=>'1m', -pady=>'1m');

$cancel_b->pack(-side=>'left', -expand=>'yes', -pady =>'10');

## Bind the Return Key to the Print Button
$cw->bind( '<Return>'=>[ sub { $print_b->flash; &Do_Print } ] );

#############################################################################
# Create Status Frame Contents

$status_l=$status_f->Label(
  -text=>'Print Status: ',
  -background=>$windowback,
  );

  
$scrolly=$status_f->Scrollbar(
  -orient=>'vert',
  -borderwidth=>0,
  -elementborderwidth=>1,
  -highlightthickness=>0,
  -background=>$buttonback,
  -troughcolor=>$windowback,
  -relief=>'flat',
  );
  
$status_t=$status_f->ROText(
  -yscrollcommand=>['set', $scrolly],
  -height=>4, 
  -relief=>'sunken', 
  -width=>'45',
  -highlightthickness=>0,
  -borderwidth=>1,
  -background=>'white',
  );

$status_l->pack(-side=>'top',-anchor=>'w');
$scrolly->pack(-side=>'right',-fill=>'y',-padx=>0,-pady=>0);
$status_t->pack(-side=>'top',-fill=>'x',-expand=>'yes',-padx=>1,-pady=>2);

$scrolly->configure(-command=>['yview', $status_t]);
#############################################################################
# Establish the User Configurable Values

$cw->ConfigSpecs( 
-Printers=>['PASSIVE', undef, undef,["lp","ps","Print-to-File"] ],
-Sizes=>['PASSIVE', undef, undef, [6,7,8,9,10,11,12,13,14] ],
-Title=>['PASSIVE', undef, undef, "Print\ \ \ \ \ \ "],
-Program=>['PASSIVE', undef, undef, 'enscript'],
-CkBtn1=>['PASSIVE', undef, undef, ' Landscape     :-r'],
-CkBtn2=>['PASSIVE', undef, undef, ' 2-Columns     :-2'],
-CkBtn3=>['PASSIVE', undef, undef, ' Line Numbers  :-C'],
-CkBtn4=>['PASSIVE', undef, undef, ' No Page Title :-B'],
-CkBtn5=>['PASSIVE', undef, undef, ' Truncate      :-c'],
-CopyArg=>['PASSIVE', undef, undef, '-n'],
-InFile=>['PASSIVE', undef, undef, undef],
-OutFile=>['PASSIVE', undef, undef, undef],
-RmFile=>['PASSIVE', undef, undef, 'no'],
-Debug=>['PASSIVE', undef, undef, 'no'],
-Fsize=>['PASSIVE', undef, undef, undef],
);
}

##############################################################################
sub Show {
  my($wd, @args)=@_;

  #############################################################################
  # Configure Subwidgets and Show the dialog

  my($printers)=$wd->cget('-Printers');
  $prt_om->configure(-options=>\@$printers);

  my($sizes)=$wd->cget('-Sizes');
  $fontsize_om->configure(-options=>\@$sizes);

  my($defsize)=$wd->cget('-Fsize');
  if ($defsize) {$size_set=$defsize};

  $wd->title($wd->{Configure}{-Title});

  $program=$wd->cget('-Program');
  $copyarg=$wd->cget('-CopyArg');
  $InFile=$wd->cget('-InFile');
  $OutFile=$wd->cget('-OutFile');
  $RmFile=$wd->cget('-RmFile');
  $Debug=$wd->cget('-Debug');

  # If no Outfile specified, then Default is $Infile.ps
  if( $OutFile eq "" ) {
    $OutFile=$InFile.".ps";
    }

  #############################################################################
  # Configure Check buttons: Label and argument
  ( $CkBtn1_L , $Opt1)=split /:/, $wd->cget('-CkBtn1');
  $CkBtn1_cb->configure( -text=>$CkBtn1_L);
  ( $CkBtn2_L , $Opt2)=split /:/, $wd->cget('-CkBtn2');
  $CkBtn2_cb->configure( -text=>$CkBtn2_L);
  ( $CkBtn3_L , $Opt3)=split /:/, $wd->cget('-CkBtn3');
  $CkBtn3_cb->configure( -text=>$CkBtn3_L);
  ( $CkBtn4_L , $Opt4)=split /:/, $wd->cget('-CkBtn4');
  $CkBtn4_cb->configure( -text=>$CkBtn4_L);
  ( $CkBtn5_L , $Opt5)=split /:/, $wd->cget('-CkBtn5');
  $CkBtn5_cb->configure( -text=>$CkBtn5_L);
  ##############################

  $wd->{'Shown'}=1;
  $wd->deiconify;
  $wd->tkwait('visibility', $wd);
  $wd->grab();
  $wd->focus();
  $wd->configure(-background=>$windowback);
  $wd->update;
  return $wd;
}#sub show


##############################################################################
sub unShow {
  my($wd)=@_;
  return if !$wd->{'Shown'};
  $wd->grab('release');
  $wd->withdraw;
  $wd->parent->update;
  $wd->{'Shown'}=0;
}#sub unshow

##############################################################################
############

sub checkprinter {
  if ("$printer_set" eq "Print-to-File") {
     $file_l->configure(-foreground=>'black');
     $file_e->configure(-state=>'normal',-foreground=>'black');
     }else{ 
        $file_l->configure(-foreground=>'grey50');
        $file_e->configure(-state=>'disabled',-foreground=>'grey50');
        }
}#sub checkprinter

sub Do_Print {
  $status_t->delete('0.0','end');
  $status_t->update;
  my ($en_opts);

  $OutFile=$file_e->get();
  $copies=$copy_e->get();

  $en_opts="";
  $en_opts .= "$Opt1 " if ($CkBtn1_set == 1);
  $en_opts .= "$Opt2 " if ($CkBtn2_set == 1);
  $en_opts .= "$Opt3 " if ($CkBtn3_set == 1);
  $en_opts .= "$Opt4 " if ($CkBtn4_set == 1);
  $en_opts .= "$Opt5 " if ($CkBtn5_set == 1);

  $en_opts .= "$copyarg$copies" if ($copies ne "");

  if ($InFile ne "" ) {
    if( $printer_set eq "Print-to-File" ) {
      if( $Debug eq "no" ) {
        $Status=`$program $en_opts -f$size_set -o$OutFile $InFile 2>&1`;
        $status_t->insert('1.1', $Status);
        }else{
          print "$program $en_opts -f$size_set -p$OutFile $InFile\n";
          }#else
      }else{
        if( $Debug eq "no" ){
          $Status=`$program $en_opts -f$size_set -P$printer_set $InFile 2>&1`;
          $status_t->insert('1.1', $Status);
          }else{
             print "$program $en_opts -f$size_set -P$printer_set $InFile\n";
             }#else
        }#else
      if( $RmFile eq "yes" ) { 
        unlink($InFile);
        }
    }else{
      $Status="No Input File Specified...";
      $status_t->insert('1.1', $Status);
      }#else
}#sub 

1;
