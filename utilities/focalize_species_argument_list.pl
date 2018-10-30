#!/usr/bin/perl -w
die "Usage:\n perl $0 <file.fcl> \n" if $#ARGV < 0 ;

use File::Basename;
use List::Uniq ':all';

$debug = "";
($debug) = grep /debug/,@ARGV;
@ARGV = grep !/debug/, @ARGV;

$path = "";
$suffix = "";

$a_file = shift (@ARGV);
$a_file = species_file_name ($a_file);

($species_name, $path, $suffix) = fileparse ($a_file,'.\w+');

open(INP, "<$a_file");
@Tout=(<INP>);
close INP;

$species= "";
$is_on = 0;
$record = 0;
@open_file_l = ();
@missing_open_file_l = ();
@argument_l = ();
%species_and_argument_list_by_argument_h = ();

foreach $_ (@Tout) {
    print "current line is >$_<" if $debug ;
    
    $record = $record + 1;
    
    if (($s) = ($_ =~ /^open "\b(\w+)\b"\;\;\s*$/)) {
	push @open_file_l, $s;
    }

    if (($s) = ($_ =~ /^species\s+\b(\w+)\b/)) {
	$is_on = 1;
	$species = $s;
	print "in species $species:\n\n";
    }
    
    if ( $is_on ) {	
	print $_;

	if (($s, $t) = ($_ =~ /^species\s+\b\w+\b\s*\(\s*(\w+) is (.*)(\,)?\s*$/)) {
	    push @argument_l, $s;
	    $species_and_argument_list_by_argument_h{$s} = $t;
	}

	if (($s, $t) = ($_ =~ /^\s*(\w+) is (.*)(\,)?\s*$/)) {
	    push @argument_l, $s;
	    $species_and_argument_list_by_argument_h{$s} = $t;
	}

	if ($_ =~ /^\s*\) =\s*$/) {
	    $is_on = 0;
	}
    }

    if (($s) = ($_ =~ /^\s*inherit \b(\w+)\b/)) {
        if ( ($s =~ /list/) || (grep /$s/, @open_file_l) ) {
#	    print "skip >$s<\n";
	}
	else { 
	    push @open_file_l, $s;
	}
    }
}

print "\n";
foreach $_ (@missing_open_file_l) { 
    print "open \"$_\";;\n";
}

print "\n";
foreach $_ (@argument_l) {
    $s = $species_and_argument_list_by_argument_h{$_};
    print "  $_ is $s\n";

    if ( ! ($s =~ /Finite_set/)){ 
	($spe = $s) =~ s/,//;

	($s = $spe) =~ s/ //g;
	$spe = $s;
	if ($s =~ /\(/) {
	    ($spe) = ($s =~ /(\w+)\(/);
	}
	elsif ($s =~ /\)/) {
	    ($spe) = ($s =~ /(\w+)\)/);
	}

	if (! grep /$spe/,@open_file_l) {
	    push @open_file_l, $spe;
	}
    }    
}

@file_l = sort (@open_file_l);
$top = pop @file_l;
@open_file_l = ($top, @file_l);
@open_file_l = uniq(@open_file_l);

print_opens (@open_file_l);

if ($species_name eq "Le_Pouvoir_reglementaire_S") {
    $abbreviated_species_name = "LPrg";
}
elsif ($species_name eq "Une_Proposition_de_loi_S") {
    $abbreviated_species_name = "UPrl";
}
elsif ($species_name eq "Une_Proposition_de_resolution_S") {
    $abbreviated_species_name = "UPrs";
}
else {
    $abbreviated_species_name = abbreviated_name ($species_name);
}

print "  $abbreviated_species_name is ";

print "${species_name} (";
print join (', ', @argument_l);
print "),\n";

sub print_opens {
    my @species_name_l = @_;
    
    print "\n";
    foreach $_ (@species_name_l) { 
	if ( $_ ne "Setoid" ) {
	    print "open \"$_\";;\n";

	}
    }
    
    print "\n";
    print "open \"${species_name}\";;\n";
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

sub clean_word_list {
    @my_word_l = @_;
    @result_l = ();
    foreach $_ (@my_word_l) {
#	print "word >$_<\n";
	if ( !(($_ eq "S")
	    || ($_ eq "d") 
	    || ($_ eq "de") 
	    || ($_ eq "des") 
	    || ($_ eq "du") 
	    || ($_ eq "l") 
	    || ($_ eq "la") 
	    || ($_ eq "les") 
	    || ($_ eq "le") 
	    || ($_ eq "un") 
	    || ($_ eq "une") 
	    )) {
	    push @result_l, $_;
	}
    }

    @result_l;
}

sub abbreviated_name {
    $my_name = shift @_;

    @word_list = split /_/, $my_name;
    @word_l = clean_word_list (@word_list);

    $count = 0;
    $result = "";
    foreach $_ (@word_l) {
	$count = $count +1;
#	$word_count = $#word_l+1;
	print "word >$_<\n" if $debug;
	$result .= substr $_,0,1;
	if ($count == 4) {
	    last;
	}
	$last_word = $_;
    }

    $end = substr ($last_word,1,(4-$count));

    $result .= $end;

}; # abbreviated_name

exit;
