#!/usr/bin/perl -w

die "Usage:\n perl $0 <species> \n" if $#ARGV < 0 ;

$a_species = shift (@ARGV);

foreach $reffil (<*.fcl>){
	
	open(INP, "<$reffil");
	@Tout=(<INP>);
	close INP;

	$is_on = 0 ;
	$record = 0;	
        $print_line = 0 ;

	foreach $_ (@Tout){

	    $record = $record + 1;
	    
	    if ($_ =~ /^species\s+\b$a_species\b/) {
		$is_on = 1;
	    }
	    
            if ($_ =~ /^end\s*$/) {
		$is_on = 0;
		print "$_" if $print_line ;
		$print_line = 0;
	    }
	    
            if ($_ =~ /^end\;\;\s*$/) {
		$is_on = 0;
		print "$_" if $print_line ;
		$print_line = 0;
	    }

	    if ( $is_on ) {	
		$print_line = 1 ;
		print "\n$reffil \n  line $record :\n\n";
		$is_on = 0;
	    }
	    
	    print "$_" if $print_line ;
	    
	}
	
}
exit;
