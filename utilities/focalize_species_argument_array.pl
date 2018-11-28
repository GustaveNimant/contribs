#!/usr/bin/perl -w

use List::Util qw(first);

$FCD = $ENV{"FCD"};

print "FCD is >$FCD<\n";

sub read_fcl_files {
    my @toutes_l = ();   

    foreach $fcl_file (<$FCD/Article_14*.fcl>) {
	print "fcl_file is >$fcl_file<\n";
	open(INP, "<$fcl_file");
	@lines_l=(<INP>);
	close INP;
	@toutes_l = (@toutes_l, @lines_l)
    }

    return @toutes_l;
}

@lines = read_fcl_files ();

$index = 0;
foreach $_ (@lines) {
    print "line $_";
    if (($abbreviation, $species_name, $t) = ($_ =~ /^\s*(\w+) is (\w+)(.*)(\,)?\s*$/)) {
	print "get line is >$_<";
	print "abbreviation is >$abbreviation<\n";
	print "species_name is >$species_name<\n";
	($s = $t) =~ s/\(//;
	($t = $s) =~ s/\)//;
	@l = split ',', $t;

	$species_name_by_abbreviation{$abbreviation} = $species_name;
	$arguments_by_abbreviation{$abbreviation} = $t;
	$argument_array_by_abbreviation{$abbreviation} = [ @l ];
    }
}

hash_print (%species_name_by_abbreviation);

@abbreviation_list = keys %species_name_by_abbreviation;
@abbreviation_list_no_set = grep !/_set/, @abbreviation_list;
@abbreviation_list_set = grep /_set/, @abbreviation_list; 

print "abbreviation_list_no_set\n";
list_print (@abbreviation_list_no_set);

hash_print (%arguments_by_abbreviation);

print "argument_array_by_abbreviation\n";
hash_of_array_print (%argument_array_by_abbreviation);

$abb = 'UFra';
%index_by_abbreviation_h = index_by_abbreviation ($abb, %argument_array_by_abbreviation);
$nam = $species_name_by_abbreviation{$abb};
$arg = $arguments_by_abbreviation{$abb};
print "idx = $idx abbreviation $abb species_name $nam arguments $arg\n";

print "hash_of index_not_set_by_abbreviation\n";
%index_not_set_by_abbreviation_h = index_by_abbreviation ($abb, %argument_array_by_abbreviation);
hash_of_array_print (%index_not_set_by_abbreviation_h);

sub index_by_abbreviation {
    my $abb = shift @_;
    %hash = @_;

    @arr = %hash{$abb};
    foreach my $n (@arr) { 
	if ($n =~ !/_set/) {
	    print "index is >$index<\n";
	    $out_hash{$abb} = $index + 1;
	}
    }
    return %out_hash;
}

sub index_of_abbreviation__ {
    my $abbr = shift @_;
    my @array = @_;

#    list_print (@array);
    
    $idx = first { $array[$_] eq $abbr } 0..$#array;
    return $idx;
}


sub is_empty_array {
# return 1 if empty
    my $here = (caller(0))[3];

    my @array = @_; 
    my $result = 0 ;

    $result = ($#array == -1 ); 
   
    print "$here: \$result = $result \n" if $debug ;

    return ( $result );
} # is_empty_array

sub is_empty_hash {
# returns 1 if empty
    my $here = (caller(0))[3];
    my (%hash) = @_;
    my $ref = \%hash ;
    my @array = () ;

    @array = keys %hash ;

    $result = ( is_empty_array (@array)) ;
    print "$here: \$result = $result \n" if $debug ;
    print "$here: \$ref = $ref \n" if $debug ;

    return ($result) ;
} # is_empty_hash

sub list_print {
    my ($here) = (caller(0))[3];
    my (@list) = @_ ;

    foreach $name (@list) {
	print "$name ";
    }

} # hash_print

sub hash_print {
    my ($here) = (caller(0))[3];
    my (%hash) = @_ ;

    die "$here: hash is empty \n" if is_empty_hash (%hash) ;
        
    foreach $name (keys(%hash)) {
	print " key \"$name\" values :";
	print "$hash{$name}\n";
    }

} # hash_print

sub hash_of_array_print {
    my ($here) = (caller(0))[3];
    my (%hash) = @_ ;

    die "$here: hash is empty \n" if is_empty_hash (%hash) ;
        
    foreach $name (keys(%hash)) {
	$l = $hash{$name};
	print " key \"$name\"";
	@l = split (',', $l);
	print " array values ", join ( ' ',@$l) ,"\n";
    }

} # hash_print

exit;
