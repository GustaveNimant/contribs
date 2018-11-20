#!/usr/bin/perl -w

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

foreach $_ (@lines) {
    if (($abbreviation, $species_name, $t) = ($_ =~ /^\s*(\w+) is (\w+) (.*)(\,)?\s*$/)) {
	print "line is >$_<";
	print "abbreviation is >$abbreviation<\n";
	print "species_name is >$species_name<\n";
	($s = $t) =~ s/\(//;
	($t = $s) =~ s/\)//;
	print "t is >$t<\n";
	$species_name_by_abbreviation{$abbreviation} = $species_name;
	$arguments_by_abbreviation{$abbreviation} = $t;
	@l = split ',', $t;
	print " list A :: ", join (':',@l) ,"\n";
	$argument_list_by_abbreviation{$abbreviation} = [ @l ];
    }
}

hash_print (%species_name_by_abbreviation);
hash_print (%arguments_by_abbreviation);

foreach $name (keys(%arguments_by_abbreviation)) {
    print " \"$name\" ";
    $t = $arguments_by_abbreviation{$name};
    @l = split (',', $t);
    print " list L ", join (' ',@l) ,"\n";
    $argument_list_by_abbreviation{$name} = [ @l ];
}

hash_of_list_print (%argument_list_by_abbreviation);

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

sub hash_print {
    my ($here) = (caller(0))[3];
    my (%hash) = @_ ;

    die "$here: hash is empty \n" if is_empty_hash (%hash) ;
        
    foreach $name (keys(%hash)) {
	print " \"$name\" ";
	print "$hash{$name}\n";
    }

} # hash_print

sub hash_of_list_print {
    my ($here) = (caller(0))[3];
    my (%hash) = @_ ;

    die "$here: hash is empty \n" if is_empty_hash (%hash) ;
        
    foreach $name (keys(%hash)) {
	$l = $hash{$name};
	print " key \"$name\" $l\n";
	@l = split (',', $l);
	print " list W ", @l ,"\n";
#	print " list ", join ( '\n',@l) ,"\n";
    }

} # hash_print

exit;
