#!/usr/bin/perl

my $BLOCK_SIZE = 4;

my $fname = $ARGV[0];
open(F, "<$fname") or die("Unable to open file $fname, $!");
binmode(F);
my $buf;
my $ct=0;

while(read(F, $buf, $BLOCK_SIZE, 0)) {
  my @bytes = split(//, $buf);
  for (my $i = 0; $i<4; $i++) {
    printf("%02x", ord($bytes[3-$i]));
  }
  $ct++;
  print " ";
  if (($ct %4)==0) {
    print "\n";
  }
}

print "\n";
close(F); 
