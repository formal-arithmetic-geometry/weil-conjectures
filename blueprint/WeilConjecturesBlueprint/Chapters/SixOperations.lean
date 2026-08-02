import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The six-operation fragment" =>

The weight-estimate machinery does not need a full six-functor formalism.
This chapter will specify the exact fragment that is consumed, per
operation, and nothing more:

* constructible Weil sheaves with Frobenius structure
  $`\varphi \colon F_X^* \mathcal{F} \cong \mathcal{F}`, stalks at
  geometric points, lisse and constructible predicates;
* $`f^*` for all morphisms (exact);
* $`R^i f_!` for separated finite-type morphisms: boundedness, the
  open/closed localization long exact sequence, composition consumed only
  through a finite Frobenius-stable filtration whose graded pieces are
  subquotients of $`R^a g_! R^b h_!` — *no spectral sequences anywhere in
  the project*;
* compact-support base change in stalk form, and along the projections
  $`\mathbb{A}^1 \times Y \to Y` (for the Fourier transform);
* the projection formula for twists by lisse sheaves pulled back from the
  base (which also eliminates every use of Künneth);
* finite pushforward and its weight behaviour;
* Artin–Schreier sheaves: trace normalization, additivity, Swan conductor
  $`1` at infinity, and the orthogonality computation on the affine line;
* affine-curve cohomology bounds ($`\Hc^0` vanishing for lisse sheaves on
  connected affine curves, $`\Hc^2` as coinvariants with a Tate twist);
* underived $`j_*` on smooth curves with inertia-invariant stalks.

Explicitly excluded from the interface: $`f^!` and Verdier duality as
functors, general $`Rf_*`, internal Hom, derived tensor beyond rank-one
kernels, Künneth, perverse $`t`-structures on general schemes, and
weights-as-structure on the categories. The main chain through the Fourier
argument is perversity-free; the curve $`t`-structure appears only inside
the internal decomposition of the local Fourier deep leaf.
