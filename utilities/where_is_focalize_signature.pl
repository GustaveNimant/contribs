#!/usr/bin/perl -w
die "Usage:\n perl $0 function \n" if $#ARGV < 0 ;

$a_function = shift (@ARGV);
$species= "";

foreach $reffil (<*.fcl>) {
	
    open(INP, "<$reffil");
    @Tout=(<INP>);
    close INP;
    
    $is_on = 0 ;
    $record = 0;	
    
    foreach $_ (@Tout) {
#	    print "current line is >$_<";
	
	$record = $record + 1;
	
	if (($s) = ($_ =~ /^species\s+\b(\w+)\b/)) {
	    $species = $s;
	}
	
	if ($_ =~ /^\s*signature\s+\b$a_function\b/) {
	    $is_on = 1;
	    print "\n$reffil line # $record\n";
	    print "in species $species:\n\n";
	}
	
	if ( $is_on ) {	
	    print $_;

	    if ($_ =~ /\;\s*$/) {
		$is_on = 0;
	    }

	}
    }
}

exit;
