# A0 round two

The fresh probe `probes/round2/A1.lean` measured the original `abbrev` source on the
v4.33.1 snapshot. `Kernel.check(value)` took 2 ms for the tensor reproducer and 1 ms
for the full consumer. Final inferred-to-declared conversion took 46,216/51,526 ms
(forward/reverse) for the tensor node and 119,953/127,832 ms for the full consumer.
The tensor node's three differing arguments took 0 ms, 1 ms, and 52,157 ms; the last
is the concrete `MonoidalCategory` instance argument. Peak RSS was 7,277,660 kB for
the probe and 11,966,564 kB for the full consumer.

The historical 49,867/50,279 ms and 131,963/121,742 ms figures are retained in the
original record as historical notes, not round-two measurements.
