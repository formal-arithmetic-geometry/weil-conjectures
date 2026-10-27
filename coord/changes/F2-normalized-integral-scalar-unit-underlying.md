# Intermediate bridge for normalized integral scalar unit

The assigned module now imports the new bridge module, which exposes one intermediate
comparison theorem used by the assigned proof. The bridge is a strictly simpler
statement: it stops at the completed `CompletedLineTensor.unit` component before the
intrinsic `sfIntegralScalarUnit` restriction. The assigned theorem combines it with
the existing canonical restriction theorem. No existing declaration signature or
upstream source module is changed. The bridge currently carries the one remaining
named proof hole for the next worker.
