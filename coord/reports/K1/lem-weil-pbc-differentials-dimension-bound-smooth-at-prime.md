## Worker report

The module `Sheaf.RingTheory.SmoothAtPrimeOfDifferentialsDimensionBound` states
`Algebra.isSmoothAtPrime_of_finrank_kaehlerDifferential_le`, with exactly one `sorry`
proof and no new definitions. No statement correction or new dependency is needed.
The repository and source checkout were read only; all written files are in this item's sandbox.

Hypothesis and conclusion correspondence:

- A field k: `{k : Type u} [Field k]`, with the universe explicitly declared.
- A finite type k-algebra S: `{S : Type v} [CommRing S] [Algebra k S]
  [Algebra.FiniteType k S]`. Independent universes u and v impose no common-universe restriction.
  `FiniteType` is unqualified in namespace `Algebra`.
- A prime ideal q: `(q : PrimeSpectrum S)` bundles precisely its ideal and primality;
  no maximality, domain, reducedness, perfectness or algebraic-closedness hypothesis is added.
- Its residue field: `q.asIdeal.ResidueField`, the residue field of `Localization.AtPrime
  q.asIdeal`, with its canonical S-algebra structure.
- Its Kahler module: `KaehlerDifferential k S`, with the canonical S-module structure.
- The fibre of the differential module: `q.asIdeal.ResidueField ⊗[S]
  KaehlerDifferential k S`. Tensoring with the residue field on the left equips it with
  the canonical residue-field module structure. This is the same fibre as the node's
  reverse-order tensor product, via `TensorProduct.comm S` with the transported
  residue-field action. No alternate definition of differentials is introduced.
- The residue-field dimension: `Module.finrank q.asIdeal.ResidueField` of that fibre.
  The finite type hypothesis implies `Algebra.EssFiniteType k S`, hence
  `KaehlerDifferential.finite` gives a finite S-module; extending scalars gives a finite
  residue-field vector space. Thus finrank denotes its actual dimension, not the
  zero fallback used by finrank on infinite-dimensional spaces. No finite-dimensional
  hypothesis has been added.
- Dimension of Spec(S) at q: `topologicalKrullDimAt q`. The underlying topological
  space of `AlgebraicGeometry.Spec (CommRingCat.of S)` is definitionally
  `PrimeSpectrum S` with its Zariski topology. This uses the topological dimension at
  the point, not the dimension of the local ring (these differ at nonclosed points).
- The displayed inequality: `hdim` casts the natural-valued finite vector-space
  dimension into `WithBot ℕ∞` and compares it by `≤` with `topologicalKrullDimAt q`.
- Smoothness at q, including the asserted principal localization: the conclusion
  `Algebra.IsSmoothAtPrime k q` is the recorded dependency's definition, literally
  `∃ g : S, g ∉ q.asIdeal ∧ Algebra.Smooth k (Localization.Away g)`.
  Consequently both the existential and its two clauses are present.

Dependency declarations read and used:

- `def-weil-pbc-finite-type-algebra`: `Algebra.FiniteType`,
  `Mathlib.RingTheory.FiniteType` (class defined by finite generation of the top subalgebra).
- `def-weil-pbc-localization-at-prime`: `Ideal.ResidueField`,
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, defined using `Localization.AtPrime`
  from `Mathlib.RingTheory.Localization.AtPrime.Basic`; the fibre-ring clause of that
  multi-clause definition is not needed for this module fibre.
- `def-weil-pbc-kahler-differentials`: `KaehlerDifferential`,
  `Mathlib.RingTheory.Kaehler.Basic`, with its universal derivation.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec`,
  `Mathlib.AlgebraicGeometry.Scheme`; its underlying prime spectrum is used directly.
  No scheme-level operations are needed, so Scheme is not imported separately.
- `def-kun-topological-dimension-at-point`: `topologicalKrullDimAt`,
  `WeilConjectures.Mathlib.Topology.KrullDimension`, the infimum of the Krull dimensions
  of all open neighbourhoods of the point (full definition read).
- `def-weil-pbc-singular-ideal`: `Algebra.IsSmoothAtPrime`,
  `Sheaf.RingTheory.SingularIdeal`, full declaration and docstring read.
- `def-weil-pbc-smooth-ring-map`: `Algebra.Smooth`,
  `Mathlib.RingTheory.Smooth.Basic`, imported by SingularIdeal, combining formal
  smoothness with finite presentation.

Edge cases checked before writing: the zero ring has no prime points and is therefore
vacuous, without an extra Nontrivial binder. The field algebra k itself has zero fibre
of differentials and dimension zero, and is smooth. Polynomial algebras at generic
points illustrate why topological dimension at the point, not local-ring dimension,
is essential. Purely inseparable finite field extensions have positive differential
dimension and zero topological dimension, so do not meet the inequality. Singular
examples such as k[e]/(e²) have a one-dimensional fibre at their unique point and
zero-dimensional spectrum, so also fail the hypothesis, in every characteristic.
No nonemptiness, positivity or characteristic restriction is imposed. Different
components and nonmaximal primes remain covered. Finite generation guarantees that
finrank cannot accidentally collapse an infinite-dimensional fibre to zero.

The local literature/stacks-project/algebra.tex is absent on this machine. Read the
full source lemma and proof online at https://stacks.math.columbia.edu/tag/00TT:
Lemma 10.140.3 explicitly has exactly these hypotheses and implication (2) => (1).
The six-step natural-language proof in the docstring follows the node's recorded
proof, including its direct fibre-base-change replacement of the preliminary
Nakayama localization. All steps name their DAG dependencies.

Searches made:

- msearch.py leanfinder: "finite type algebra over field smooth at prime if dimension
  Kahler differentials residue field at most topological dimension at point".
  Eight hits: IsSmoothAt, Smooth, smoothLocus, standard-smooth and relative-dimension
  declarations. None states this implication or uses the topological point dimension.
- msearch.py loogle: "Algebra.IsSmoothAt, KaehlerDifferential". Zero hits.
- msearch.py leansearch: "finite type algebra field smooth at prime dimension Kahler
  differentials residue field bound". Unavailable (Internal Server Error); no verdict.
- msearch.py grep: "IsSmoothAt.*(dim|rank)|finrank.*Kaehler|Kaehler.*finrank".
  Zero Mathlib hits.
- rg across WeilConjectures and lean/Sheaf for the item id, topologicalKrullDimAt,
  finrank.*Kaehler, Kaehler.*finrank: the point-dimension definition and unrelated
  smooth-relative-dimension results; project CartierEquality uses differential
  finrank but has a different statement; ClosedPointDimensionLocalRing equates
  two dimensions only at maximal ideals. No existing statement matches this node.
- rg across dag/lean_names_upstream.json, WeilConjectures and lean/Sheaf for
  isSmoothAtPrime_of_finrank, IsSmoothAtPrime and the finrank/differential patterns:
  no collision for the new name; IsSmoothAtPrime is the usable recorded definition
  in SingularIdeal and is imported, not duplicated.

Validation: scompile.py compiled the module on the server in 1.4 seconds, with no
errors or warnings. No local compilation, library build or delivery push was run.

## Second reading by K1

I independently read the node statement, its Stacks source (Algebra, Tag 00TT,
Lemma 10.140.3, implication (2) => (1)), and
`Sheaf/RingTheory/SmoothAtPrimeOfDifferentialsDimensionBound.lean`.
The correspondence is:

- The field `k` is `{k : Type u} [Field k]`; this introduces exactly the source's
  arbitrary field, with no characteristic restriction.
- The finite type algebra `S` is `{S : Type v} [CommRing S] [Algebra k S]
  [FiniteType k S]`; the independent universes permit all source cases.
- The prime is `(q : PrimeSpectrum S)`, so `q.asIdeal` is exactly the source
  prime ideal, with no maximality, reducedness, or domain assumption.
- The residue field is `q.asIdeal.ResidueField`, matching
  `\kappa(\mathfrak q)` and carrying its canonical `S`-algebra structure.
- The Kähler module is `KaehlerDifferential k S`, matching `\Omega_{S/k}`.
- The fibre is `q.asIdeal.ResidueField ⊗[S] KaehlerDifferential k S`; the
  canonical tensor commutation is the source's `KaehlerDifferential k S ⊗[S]
  \kappa(\mathfrak q)` and carries the same residue-field vector-space
  structure.
- `Module.finrank` of that fibre is cast to `WithBot ℕ∞`, exactly the dimension
  in the node's inequality; finite type supplies the needed finite module.
- `topologicalKrullDimAt q` is the pointwise Krull dimension of `Spec S`, the
  source's `\dim_{\mathfrak q}(\operatorname{Spec}S)`.
- `hdim` states precisely the required `≤` inequality.
- The conclusion `IsSmoothAtPrime k q` unfolds to `∃ g : S, g ∉ q.asIdeal ∧
  Smooth k (Localization.Away g)`, exactly the source's smoothness-at-`q`
  assertion.

No hypotheses or conclusion clauses were added, dropped, strengthened, or
weakened. The zero ring is vacuous because it has no prime spectrum; `n = 0`
and zero differential fibres are covered by `finrank`; empty schemes and
nonclosed primes are covered by the bundled prime and pointwise dimension;
characteristic is unrestricted. The tensor-factor order is only the canonical
commutation isomorphism, with no change of mathematical object.

I searched Mathlib and the project with the worker's LeanFinder/Loogle/grep
queries and additional searches for `finrank`, `KaehlerDifferential`,
`IsSmoothAtPrime`, and `topologicalKrullDimAt`; no existing declaration states
this criterion. The source repository and `dag/lean_names_upstream.json` also
contain no collision. The recorded dependency declarations were opened and
match their nodes, including `Algebra.IsSmoothAtPrime` and
`topologicalKrullDimAt`.

There were no mismatches to repair. The module compiled cleanly with
`scompile.py`; all citers continue to use the same implication, so their
`holds` verdict is true: `lem-weil-pbc-regular-local-separable-residue-smooth`,
`lem-weil-pbc-h1-cotangent-flat-base-change`,
`lem-weil-pbc-smooth-at-prime-field-extension-descent`, and
`lem-weil-pbc-smooth-at-maximal-ideal-alg-closed-differentials-bound`.
