#!/usr/bin/perl

my $filename = $ARGV[0];
my $cnt=0;

open(my $fh, "<:raw", $filename) or die "Cannot open file: $!";
$num64 = 0;
while(read($fh, $buf, 1)) {
  $shamt = 8*($cnt % 8);
  $w1 = ord($buf);
  # printf("%02x\n", $w1);
  $num64 += ($w1 << $shamt);
  $cnt ++;
  if ($cnt %8 == 0) {
    printf("%016x\n", $num64);
    $num64 = 0;
  }
}
close(F); 

if ($cnt %8 != 0) {printf("%016x\n", $num64);}

