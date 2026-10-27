## Worker report

The module `Sheaf.AlgebraicGeometry.FppfLiftsFiniteAffineCharts` states
`AlgebraicGeometry.Scheme.exists_finite_affine_charts_of_fppf_lifts`, with its entire
proof `sorry`. There are no definitions, auxiliary postponed theorems, new nodes,
dependency repairs, or statement corrections.

Clause-by-clause correspondence:

- Schemes and arbitrary morphism a: `{X Y : Scheme.{u}} (a : X ⟶ Y)`. There is no
  flatness, finite presentation, separation, or quasi-compactness hypothesis on a.
- The size convention is expressed by explicit universes `u v`: schemes have
  universe u and the arbitrary set of covering indices is `I : Type v`.
- The set-indexed fppf covering is `Yᵢ`, `q`, and
  `hq : Presieve.ofArrows Yᵢ q ∈ fppfPrecoverage Y`. This precoverage means jointly
  surjective flat locally finitely presented maps, exactly the dependency's notion.
- The lifts are `s : ∀ i : I, Yᵢ i ⟶ X` and
  `hs : ∀ i : I, s i ≫ a = q i`.
- Every affine open of Y is `(V : Y.Opens) (hV : IsAffineOpen V)`.
- The nonnegative integer is the existential `n : ℕ`, and its n charts are indexed
  by `Fin n`, equivalent to the node's 1 through n indexing.
- Affine source opens are `U : Fin n → X.Opens` and
  `∀ j : Fin n, IsAffineOpen (U j)`.
- Their image containment is `e : ∀ j : Fin n, U j ≤ a ⁻¹ᵁ V`. The exact restriction
  of a is `a.resLE V (U j) (e j)`.
- The affine covering schemes are `T : Fin n → Scheme.{u}` and
  `∀ j : Fin n, IsAffine (T j)`.
- The two displayed families of maps are `t` and `r`. The geometric factorization
  is `r j = t j ≫ a.resLE V (U j) (e j)`.
- Their fppf covering condition is
  `Presieve.ofArrows T r ∈ fppfPrecoverage V.toScheme`.
- There is no separate arbitrary choice of coordinate rings: B is
  `Γ(V.toScheme, ⊤)`, A_j is `Γ((U j).toScheme, ⊤)`, and D_j is `Γ(T j, ⊤)`.
  `IsAffineOpen` and `IsAffine` identify these schemes canonically with their
  spectra via Mathlib's `Scheme.isoSpec`. Thus the global-section formulation
  expresses the stated affine schemes and not some replacement objects.
- The induced maps B to A_j to D_j are the respective `appTop` maps. Their
  factorization is explicitly included as
  `(r j).appTop = (a.resLE V (U j) (e j)).appTop ≫ (t j).appTop`.
- Each B to D_j is flat and finitely presented in the conjunct
  `(r j).appTop.hom.Flat ∧ (r j).appTop.hom.FinitePresentation`.
- D is the actual product ring `∀ j : Fin n, Γ(T j, ⊤)`. Its coordinate map is
  `RingHom.pi (fun j : Fin n ↦ (r j).appTop.hom)`. Both its faithful flatness and
  its finite presentation occur explicitly as consecutive conjuncts.
- The empty V case is not merely permitted implicitly. The concluding implication
  `IsEmpty V.toScheme → n = 0 ∧ Subsingleton Γ(V.toScheme, ⊤) ∧
  Subsingleton (∀ j : Fin n, Γ(T j, ⊤))` says that the witnesses can be chosen with
  zero charts and that both B and D are zero rings. `Subsingleton` is the usual
  invariant expression that a commutative ring is the zero ring.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme.Hom`, `AlgebraicGeometry.Spec`, and `Spec.map`.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfPrecoverage`; the site's node
  records this together with `Scheme.fppfTopology`.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat`, using `Module.Flat`.
- `Mathlib.RingTheory.FinitePresentation`: `Algebra.FinitePresentation` and its
  bare-ring-map form `RingHom.FinitePresentation` already listed in the node's
  Mathlib match.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`, both named
  by the dependency record/match.
- `def-weil-size-convention` has no mathematical declaration; its record explicitly
  instructs consumers to bind universes, as this file does.

Additional statement APIs are the existing `IsAffineOpen`, `IsAffine`,
`Scheme.Hom.resLE`, `Scheme.Hom.appTop`, and `RingHom.pi`. Proof imports expose
pullbacks, the affine-opens basis, open-immersion factorization, the affine flatness
and finite-presentation criteria, finite type, the algebraic-space covering
calculus and its scheme equivalence, and
`AlgebraicGeometry.finiteAffineFamily_fppfAlgebra` from
`Sheaf.AlgebraicGeometry.Morphisms.FiniteAffineFamilyFppfAlgebra`.
The finite affine refinement declaration
`Scheme.exists_finite_fppf_affine_open_refinement` is imported from
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`: it is signature-identical
with the older recorded `Sheaf.AlgebraicGeometry.FppfAffineRefinement` declaration.
The covering-calculus module already imports the upstream module transitively, so
using upstream avoids loading two declarations of that name. No dependency
interface changes are required.

Edge cases checked before writing: empty V, n = 0, empty initial I, empty covering
members, arbitrary initial index universe v, and non-flat/non-quasi-compact a.
For empty V, the empty source family covers the empty scheme; B and the empty
product D are zero. The identity zero-ring map is flat, faithfully flat, and
finitely presented. Conversely n = 0 cannot cover nonempty V. If I is empty,
the covering hypothesis already forces Y empty, so all target opens are empty.
Empty factors in a nonempty finite family add no points and are allowed. There
is no independent universe for test rings that could make a hypothesis vacuous.

Sources opened: `literature/stacks-project/descent.tex`, `lemma-curiosity`
(Tag 06NB), especially its affine preparation and product-map sentence; and
`literature/stacks-project/topologies.tex`, `lemma-fppf-affine` (Tag 021P).
The node matches these paragraphs; no source-based correction is necessary.

Searches (2026-10-24, prescribed msearch wrapper):

- LeanFinder: "Finite affine fppf cover subordinate to local lifts through affine
  opens of a scheme morphism" returned 8 hits, including `Scheme.AffineCover`
  and `Scheme.OpenCover.affineRefinement`, not this statement.
- Loogle: `AlgebraicGeometry.Scheme.fppfPrecoverage, RingHom.pi` returned 0 hits.
- Mathlib grep: `fppf|affine.*refinement` in `AlgebraicGeometry/Sites` returned 5
  hits, the fppf precoverage/topology definitions and their surrounding lemmas.
- LeanSearch: "An fppf locally split scheme morphism admits finite affine fppf
  covering charts over each affine open" returned 8 hits on ordinary affine
  covers and affine-property criteria, not this statement.
- Direct rg in `lean/WeilConjectures` and `lean/Sheaf` for
  `fppf.*(lift|affine)|finite.*fppf|lem-sfb-fppf-lifts-finite-affine-charts` found
  the upstream finite affine refinement and the related finite affine source
  charts theorem. The latter assumes the source map itself flat, surjective and
  locally finitely presented and has a different conclusion; it cannot replace
  this lemma about an arbitrary morphism with local lifts.
- Direct name search for `exists_finite_affine_charts_of_fppf_lifts` in Mathlib,
  both project roots and `dag/lean_names_upstream.json` found no existing name.

No STATEMENT-DISPUTED flag or node fault.

## Second reading by Q04

Author's second check, not an independent review: I reread the complete node and
Lean signature together. The cover assumption remains a family cover (not a
single surjection), lifts are maps into X, the U_j are open in X, and the T_j
need only be affine schemes. Neither U_j nor a is assumed fppf. The displayed
restriction and both map directions agree with contravariance on sections.
The product map is built from r_j, not arbitrary maps, and both ring-property
clauses are present. The final implication chooses n = 0 for empty V rather
than imposing nonemptiness on V or I. All binders and universes are explicit.
No mathematical mismatch or correction was found. Independent delivery review
belongs to the maintainer under this dispatch brief.
