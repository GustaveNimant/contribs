#!/usr/bin/perl -w
die "Usage:\n perl $0 <file.fcl> \n" if $#ARGV < 0 ;

use File::Basename;
use List::Uniq ':all';

$debug = "";
($debug) = grep /debug/,@ARGV;
@ARGV = grep !/debug/, @ARGV;

$a_file = shift (@ARGV);
$a_file = species_file_name ($a_file);

open(INP, "<$a_file");
@lines_l=(<INP>);
close INP;

sub open_file_names {
    my @lines_l = @_;
    my @open_lines_l = ();
    my @open_files_l = ();

    @open_lines_l = grep /^open "\b(\w+)\b"\;\;\s*$/, @lines_l;
    
    @open_files_l = ();
    foreach $_ (@open_lines_l) { 
	print "$_" if ($debug);
	($file) = ($_ =~ /^open "\b(\w+)\b"\;\;\s*$/);
	push @open_files_l, $file;
    }
    @open_files_l;
}

@open_files_l = open_file_names (@lines_l);

if ($debug) {
    print "\n";
    print join ("\n", @open_files_l);
    print "\n";
}

@lowercase_file_l = lowercase_file_names (@open_files_l);
@non_lowercase_file_l = non_lowercase_file_names (@open_files_l);

print_opens (@lowercase_file_l);

print_opens (@non_lowercase_file_l);

sub lowercase_file_names {
    my @files_l = @_;
    my @lc_l = ();
    foreach $_ (@files_l) { 
	print "$_" if ($debug);
	if (lc $_ eq $_) {
	    push @lc_l, $_;
	}
    }
    sort @lc_l;
}

sub non_lowercase_file_names {
    my @files_l = @_;
    my @lc_l = ();
    foreach $_ (@files_l) { 
	print "$_" if ($debug);
	if (lc $_ ne $_) {
	    push @lc_l, $_;
	}
    }
    sort @lc_l;
}

sub print_opens {
    my @species_name_l = @_;
    
    foreach $_ (@species_name_l) { 
	if ( $_ ne "Setoid" ) {
	    if ($_ =~ /_subtype/) {
		if (! grep /Les_Fonctions_de_conversion/, @species_name_l) {
		    print "open \"Les_Fonctions_de_conversion\";;\n";
		}
	    }
	    else {
		print "open \"$_\";;\n";
	    }
	}
    }
    print "\n";
}

sub species_file_name {
    my $file = shift @_;

# print "file >$file<\n";
    if ($file =~ /_S\.fcl$/) {
    }
    elsif ($file =~ /_$/) {
	$file = $file . "S.fcl";
    }
    elsif ($file =~ /_S$/) {
	$file = $file . ".fcl";
    }
    elsif ($file =~ /_S\.$/) {
    $file = $file . "fcl";
    }
    elsif (!($file =~ /_S\.fcl/) ) {
	$file = $file . "_S.fcl";
    }
    else {
	die "Usage:\n perl $0 <file.fcl> \n" ;
    }
    
    if ( ! ( -s $file )) {
	die "input file >$file< does not exist\n";
    }

    $file;

} # species_file_name

exit;
