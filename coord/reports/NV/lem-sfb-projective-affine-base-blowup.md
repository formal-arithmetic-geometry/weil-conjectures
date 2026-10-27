## Worker report

This delivery states `AlgebraicGeometry.isHProjective_blowupMap_and_comp_of_affine_base`
in `Sheaf.AlgebraicGeometry.ProjectiveAffineBaseBlowup`. Its only theorem has proof
`sorry`; no definition, proof, auxiliary theorem, new node, dependency repair, or
statement correction is introduced. The copied node changes only `lean`.

Q07's reviewed delivery is a stage-1 split with no Lean attachment. It supplies the
seven-step proof plan used here. The earlier assignment-superseded message does
not establish a competing stage-2 declaration; no reviewed proof split is changed.

Clause-by-clause correspondence:

| Node hypothesis or conclusion | Lean rendering |
| --- | --- |
| A commutative ring A | `(A : Type u) [CommRing A]` |
| A is Noetherian | `[IsNoetherianRing A]` |
| S = Spec A | `Spec (CommRingCat.of A)` |
| A scheme X and morphism f : X → S | `{X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))` |
| f factors through finite projective space by a closed immersion | `[IsHProjective f]`, using the recorded upstream class |
| A quasi-coherent ideal in O_X | `(I : X.IdealSheafData)` and its canonical module `I.toModules` |
| The ideal is quasi-coherent and finite type | `(hI : I.toModules.IsQuasiCoherentFiniteType)` |
| B is the ordinary blowup and b its structure morphism | the canonical `I.blowup` and `I.blowupMap` from `WeilConjectures.Blowup.Gluing` |
| b is H-projective | `IsHProjective I.blowupMap` |
| f b is H-projective | `IsHProjective (I.blowupMap ≫ f)` |
| Both conclusions | their conjunction `∧` |
| Zero/unit ideals and empty blowups allowed | no nonzero, proper-ideal or nonempty hypothesis |
| No integrality, regularity or excellence assumption | no such binder or class instance |

The existing `IsHProjective` class quantifies over finite coordinate types. This
is the dependency node's documented equivalent formulation of P^N: a nonempty
finite type has size N+1, while an empty coordinate type gives an empty source,
which also embeds into P^0. It does not omit any node case. All universe variables
and object variables are explicit; `set_option autoImplicit false` is enabled.
`IsQuasiCoherentFiniteType` is the recorded conjunction of Mathlib's
`SheafOfModules.IsQuasicoherent` and `SheafOfModules.IsFiniteType`, rather than a
finite-presentation replacement. `I.toModules` is the canonical kernel of the
map to the structure sheaf of the closed subscheme, and not an independently
chosen sheaf. Quasi-coherence is inherent in ideal-sheaf data; keeping it in the
recorded conjunction renders the node's exact finite-type module interface.

Statement dependencies read and used:

- `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-weil-closed-immersion`: `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`, `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`, `AlgebraicGeometry.Scheme.IdealSheafData.blowup`.

`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module` supplies the
canonical `AlgebraicGeometry.Scheme.IdealSheafData.toModules` used with the
finite-type module predicate. The blowup's structural map is `blowupMap`, not
the affine-chart inclusion `blowupι` (an older audit listed the latter too).
All recorded statement-dependency declarations and docstrings were read in
the named read-only live source clone. Modules for stated proof dependencies
are plain imports; their seven-step proof plan is included in the theorem's
docstring. The public imports expose only the notions used by the signature.

Source and edge-case check:

I read local Stacks `divisors.tex`, `lemma-blowing-up-projective` (02NS), and
`morphisms.tex`, `lemma-projective-over-quasi-projective-is-H-projective`
(087S) and `lemma-H-projective-composition` (01WE). The first proves bundle
projectivity from Sym(I) → Rees(I); the second converts it to H-projectivity
when the base X has an ample invertible sheaf; the affine-base embedding of X
supplies such a sheaf. The third supplies the composite conclusion. These are
exactly the reviewed seven steps, preserved in the docstring.

- I = 0: Rees has zero positive-degree pieces, so Proj is empty. The statement
  permits this and retains both projectivity conclusions.
- I = O_X: Rees is locally R[t], and Proj R[t] → Spec R is the identity.
- X empty, and A the zero ring: neither is excluded by an extra binder.
- Nilpotent I, e.g. (epsilon) on Spec(k[epsilon]/epsilon^2): Proj can be empty;
  no use of an integral domain or non-zero-divisor is implicit.
- X need not be affine: its given H-projectivity over Spec A supplies absolute
  ampleness. No global finite set of generators of I is assumed.
- A need not be reduced, a field, regular or excellent. No new hypothesis is
  introduced. The Noetherian assumption is retained as the node states it.

Searches made before writing:

- msearch.py leanfinder, query `The blowup of a finite type quasi coherent ideal
  on a projective scheme over a Noetherian affine scheme is H projective over
  the scheme and the affine base`: 8 hits about absolute Proj properness,
  construction, charts and finite type, none with this H-projectivity statement.
- msearch.py loogle, query `IsHProjective, blowupι`: 0 hits; the service reports
  unknown identifier IsHProjective, so this alone is not evidence of absence.
- msearch.py grep, query
  `isHProjective.*blowup|blowup.*isHProjective|IsHProjective.*blowup`: 0 hits.
- msearch.py leansearch, query `The blowup of a finite type quasi coherent ideal
  on a scheme projective over an affine Noetherian scheme is projective over
  the scheme and its affine base`: 8 hits about absolute Proj separation,
  charts, locally finite type and quasi-compactness; no exact match.
- rg with H-projectivity/blowup patterns in both `lean/WeilConjectures` and
  `lean/Sheaf`: only a specialized flatification conclusion and downstream
  docstrings; no theorem with these hypotheses and both conclusions.
- rg of the exact item id in `lean/WeilConjectures`: no hit.
- Read `WeilConjectures.Blowup.Proper`: it proves properness by affine locality
  and expressly states that global blowup projectivity is unformalized.
  Affine blowup embeddings do not state the conclusion for non-affine X.

No statement dispute or node fault was found. No statement correction is made.

Validation: the delivered module is checked using the prescribed scompile.py;
the delivery dry run and final delivery are performed using deliver2.py.

## Second reading by NV

Self-review only: the dispatcher explicitly prohibits starting another agent;
the maintainer supplies the independent delivery review. I reread the actual
node and the actual generated signature clause by clause using the table above.
Both conclusions use the canonical blowup map and retain the original affine
Noetherian and H-projective hypotheses. No mismatch was found. In particular,
I checked that `blowupι` is a chart inclusion and used `blowupMap` instead.
This section does not claim a second independent worker has reviewed the file.
