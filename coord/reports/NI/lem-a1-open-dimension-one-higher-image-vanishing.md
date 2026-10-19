## Worker report

The module `Sheaf.AlgebraicGeometry.OpenDimOneHigherDirectImageVanishing` states
`AlgebraicGeometry.isZero_higherDirectImage_open_of_stalk_dimension_le_one`, with its
proof postponed by `sorry`. There are no definitions, helper theorems, new nodes,
dependency repairs, or statement corrections.

Source checked: `literature/stacks-project/varieties.tex`, Tag 09N8,
`lemma-affine`, statement and full proof at lines 7747–7780. The source has exactly
the local-ring hypotheses in the node. In particular, local rings being Noetherian
does not get replaced by the stronger assertion that X is locally Noetherian.

Each hypothesis and clause is rendered as follows:

- A scheme X: `(X : Scheme.{u})`.
- Every local ring O_{X,x} is Noetherian:
  `(hnoeth : ∀ x : X, IsNoetherianRing (X.presheaf.stalk x))`. The presheaf here is
  the structure presheaf, so these are ring stalks, not stalks of F.
- Every such local ring has ring Krull dimension at most one:
  `(hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1)`.
  `ringKrullDim` takes values in `WithBot ℕ∞`, retaining zero-ring and infinite cases.
- An open U and its retrocompactness: `(U : X.Opens)` and
  `(hU : IsRetrocompact (U : Set X))`. Mathlib's definition is literally
  `∀ ⦃V⦄, IsCompact V → IsOpen V → IsCompact (U ∩ V)`; compactness requires no
  separation axiom. No quasi-compactness of X or U is imposed.
- The open subscheme and its inclusion j are the canonical `U.toScheme` and `U.ι`.
  Mathlib provides the open-immersion instance for this inclusion. There is no
  arbitrary morphism replacing j.
- An O_U-module F is
  `(F : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))`.
  Quasi-coherence is exactly `(hF : F.IsQuasicoherent)`, the shared Mathlib notion;
  no finite-type or coherence assumption is imposed.
- Positive integer degree p: `(p : ℕ) (hp : 0 < p)`. Ordinary right derived functors
  are indexed by naturals, and every positive integer is uniquely such a natural.
  Thus this includes precisely all the integer degrees asserted in the node.
- The conclusion R^p j_* F = 0 is categorical zero-objecthood
  `IsZero (((RingedSpace.moduleDirectImage U.ι.toLRSHom.toShHom).rightDerived p).obj F)`.
  These are exactly the ordinary right derived functors in the recorded
  `pqf-def-cohomology` interface. Enough injectives is supplied by the shared
  Grothendieck instance, so no extra resolution or derived-category hypothesis is added.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `WeilConjectures.Topology.PresheafModuleStalkFunctor`:
  `PresheafOfModules.moduleStalkFunctor`; its carrier is the existing Mathlib stalk.
  Only structure-ring stalks occur in the statement; the recorded module is imported.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace`, the underlying compactness convention.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType` imports the shared
  `SheafOfModules.IsQuasicoherent` notion used here. Its newly recorded finite-type
  conjunction is not needed by this node, which only requires quasi-coherence.
- `WeilConjectures.AlgebraicGeometry.PQFCohomology`:
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`, identifying higher direct
  images with `(RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p`.
  The direct-image definition and Grothendieck instance were also read in the live
  `WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage` source.

All statement dependency modules are public imports. The available proof dependencies
are ordinary imports: affine-open stalk localization (`Mathlib.AlgebraicGeometry.AffineScheme`),
localization flatness (`Mathlib.RingTheory.Flat.Localization`), the recorded flat-base-change
module (`WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`), and affine vanishing
(`WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineVanishing`). The latter
is the current live module in the closed audit; its full signature was read through
`scompile.py --source`. The recorded EulerChar declaration `finrankH_pullback` is a
field-extension dimension statement, not the full general flat base-change interface;
this is a proof-interface limitation for stage 3, not a notion used to type this statement.
The local-spectrum classification proof dependency has no Lean record yet, so no import
is available or needed to type this statement. Its use is included in the proof docstring.

Edge cases checked against the source proof: X empty (local hypotheses vacuous and the
only open is empty), U empty (zero sheaf category), U = X (identity inclusion), F = 0,
zero-dimensional local rings (including fields), arbitrary nonreduced local rings of
dimension one, and p = 1. Degree zero is deliberately excluded: its direct image can
be nonzero. No nonempty, reduced, irreducible, separated, affine, or global Noetherian
hypothesis occurs. Universe u is explicitly bound, consistently with the recorded
module-sheaf and ordinary higher-direct-image interfaces. No auto-bound variable remains.

Searches for an existing declaration:

- `msearch.py` leanfinder: "higher direct images of quasi-coherent modules vanish for a
  retrocompact open in a scheme with Noetherian local rings of dimension at most one".
  Eight results about qcqs sections and quasi-compact open immersions, no match.
- `msearch.py` loogle:
  `AlgebraicGeometry.IsOpenImmersion, CategoryTheory.Functor.rightDerived`.
  Zero hits.
- `msearch.py` grep: `retrocompact|09N8|dimension.*higherDirectImage` in AlgebraicGeometry.
  Five hits about basic opens and finite presentation, none stating this vanishing.
- `msearch.py` leansearch: "higher direct image vanishing retrocompact open local rings
  dimension at most one". Eight results about retrocompactness, stalks, and sections;
  no matching vanishing theorem.
- `rg` in the upstream WeilConjectures and side Sheaf trees for the item id,
  retrocompactness, and higherDirectImage: affine vanishing exists, while no theorem
  states the present local-dimension assertion. The citer module
  `Sheaf.AlgebraicGeometry.NoetherianAffineDimOneOpen` only refers to this node in its
  proof docstring. Exact proposed declaration/module name searches in Mathlib,
  WeilConjectures, Sheaf, and `dag/lean_names_upstream.json` returned no matches.

There is no mathematical statement dispute. The theorem docstring reproduces all three
DAG proof steps and their named inputs. Only the item's `lean` record changes.

## Second reading by NI

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
