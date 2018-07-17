#!/usr/bin/perl -w

use File::Basename;

open(OUT, ">c.sh");

foreach $reffil (<*.fcl>){

    ($name, $path, $suffix) = fileparse($reffil,'.\w+');

    open(INP, "<$reffil");
    @Tout=(<INP>);
    close INP;
    
#    print "\nname is $name\n";
    ($first, $second, @item_l) = split ('_', $name) ;	

#    print "first $first\n";
#    print "second $second\n";
    $reste = join ("_", @item_l);
#    print "reste $reste\n"; 

    $First = ucfirst($first);
    $Second = ucfirst($second);
    @Name_l =  ($First, $Second, @item_l);
    $Name = join ("_", @Name_l);

    $Reffil = $Name . $suffix;
#    print "$name has been renamed as $Name\n"; 

    $Text = join ('', @Tout);
    $Text =~ s/$name/$Name/g;

    rename $reffil, $Reffil;

    $command = "modify_word.pl $name $Name *.fcl *keep\n";
    print OUT "$command";
}
close OUT;

exit;
