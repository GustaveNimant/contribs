#!/usr/bin/perl -w
die "Usage:\n perl $0 <string with blanks>\n" if $#ARGV < 0 ;

$debug = "";
($debug) = grep /debug/,@ARGV;
@ARGV = grep !/debug/, @ARGV;

$a_string = shift (@ARGV);

$a_string = remove_accent ($a_string);
$a_string = to_lowercase ($a_string);
$a_string = replace_some_characters_by_blank ($a_string);
$a_string = replace_blank_by_underscore_character ($a_string);

print " $a_string\n";

sub remove_accent {
    my $string = shift @_;
    
    $string =~ s/ö/o/g;
    $string =~ s/ô/o/g;
    $string =~ s/é/e/g;
    $string =~ s/è/e/g;
    $string =~ s/ê/e/g;
    $string =~ s/â/a/g;
    $string =~ s/à/a/g;
    $string =~ s/â/a/g;
    $string =~ s/ü/u/g;
    $string =~ s/ù/u/g;
    $string =~ s/ç/c/g;
    $string =~ s/î/i/g;
    $string =~ s/ï/i/g;
    $string =~ s/É/E/g;

    $string;
}

sub to_lowercase {
    my $string = shift @_;
    
    $string = lc $string;
}

sub replace_some_characters_by_blank {
    my $string = shift @_;

    $string =~ s/\:/ /g;
    $string =~ s/\·/ /g;
    $string =~ s/\,/ /g;
    $string =~ s/\;/ /g;
    $string =~ s/\'/ /g;
    $string =~ s/\[/ /g;
    $string =~ s/\]/ /g;
    $string =~ s/\(/ /g;
    $string =~ s/\)/ /g;
    $string =~ s/\./ /g;
    $string =~ s/-/ /g;
    $string =~ s/\+/ /g;

    $string;
}

sub replace_blank_by_underscore_character {
    my $string = shift @_;
    
    @word_l = split (' ', $string);
    $string = join ('_', @word_l);

    $string;
}

exit;
