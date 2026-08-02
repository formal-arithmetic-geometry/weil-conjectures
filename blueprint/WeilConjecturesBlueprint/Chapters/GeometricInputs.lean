import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Deep geometric inputs" =>

This chapter will hold the major deep inputs of the realization layer and
the deep leaves of the weight machinery, each with the narrowest statement
that unlocks its consumers, an internal decomposition, and an explicit
elimination plan:

* *Proper base change* with finite coefficients, and the finiteness and
  constructibility of $`R f_!` (the realization debts of the six-operation
  fragment);
* *Duality realization*: Kummer classes, Thom classes and deformation to
  the normal cone, the trace map, absolute Poincaré duality and curve
  duality;
* *Trace-formula realization*: the Lefschetz–Verdier trace formula with
  finite coefficients and Frobenius local terms (the differential of
  Frobenius vanishes, so fixed points are isolated with multiplicity one);
* *Real-sheaf purity* (PUR): every irreducible lisse subquotient of an
  $`\iota`-real lisse Weil sheaf on a smooth curve is punctually
  $`\iota`-pure — proved by the positivity route (even tensor powers,
  radius comparison, determinant weights), with geometric class field
  theory for rank one as the terminal sub-leaf;
* *Boundary monodromy* (MON): weight bounds for inertia invariants
  ($`\leq w`) and for $`R^1 j_*` ($`\geq w + 2`) on punctured curves —
  both provable by elementary semicontinuity given the trace formula — and
  the genuinely deep Jordan-block purity for length-two unipotent quotients;
* *Local Fourier theory* (LFT): the stationary-phase exact sequence for
  the Fourier–Deligne transform of a middle extension on the affine line;
* *Tame reduction* (TAME): the relative-curve normal form, eliminable by
  switching to the real-envelope variant of the relative curve argument;
* scheme-theoretic prerequisites: Nagata compactification, relative Noether
  normalization, generic smoothness and stratifications, smooth completion
  of curves, Zariski's main theorem for quasi-finite morphisms.

Each deep leaf will be recorded as a temporary-axiom node with its
downstream consumers made explicit, so the dependency graph shows exactly
which final conclusions rest on which unproved inputs at every stage.
