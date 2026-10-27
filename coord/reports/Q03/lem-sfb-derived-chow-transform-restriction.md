## Worker report

The module `Sheaf.AlgebraicGeometry.DerivedChowTransformRestriction` states
`AlgebraicGeometry.derivedChow_transform_restriction`, with its proof postponed by
`sorry`. It follows the displayed derived isomorphism of Stacks Tag 0CSK,
`more-morphisms.tex`, lemma-compute-Fourier-Mukai-for-derived-chow. I read that
lemma and its proof, the target node and every statement dependency's statement,
Lean record, and recorded source declaration/docstring. No statement change,
new node, or dependency replacement is needed.

Clause-by-clause correspondence:

- A commutative ring is `(A : Type u) [CommRing A]`; `n : ℕ` retains n = 0.
- The structure map is `f : X ⟶ Spec (.of A)`. Separatedness is `[IsSeparated f]`.
  Finite presentation is the project's specified conjunction
  `[LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]`.
- `eP : P ≅ Proj.projectiveSpaceOverAffine (ULift.{u} (Fin (n + 1))) A`
  identifies P with exactly Proj of the polynomial ring in n+1 homogeneous
  coordinates, rather than taking an arbitrary proper ambient scheme. The
  structure map of P is `eP.hom ≫ Proj.projectiveSpaceOverAffineToSpec ... A`.
  Naming P with its identification merely allows the usual replacement by an
  isomorphic scheme; taking eP = Iso.refl gives the literal specified P.
- `p : T ⟶ X`, `q : T ⟶ P`, and `_hT : IsPullback p q f (...)` say precisely
  that T with those projections is the fibre product over A. This is the
  universal property of the recorded fibre-product node and includes its
  chosen `pullback` as a particular instance. No arbitrary unrelated maps
  can satisfy the premise in place of the product projections.
- The graph is `h : Z ⟶ T` with `[IsClosedImmersion h]`.
  The composites b and c are written out as `h ≫ p` and `h ≫ q`.
- `U : X.Opens`, `V : P.Opens`, `W : Z.Opens`, and the equalities `hWU`, `hWV`
  give exactly W = b^{-1}(U) = c^{-1}(V). They impose no compactness on the opens.
- The actual restricted maps are `(h ≫ p).resLE U W hWU.le` and
  `(h ≫ q).resLE V W hWV.le`; `resLE` is the existing Mathlib source/target
  restriction. Their classes `IsIso` and `IsClosedImmersion` give the two
  stated properties on W.
- `E : schemeDerivedCategory T` has no boundedness, pseudo-coherence or
  quasi-coherence premise. `_hE : Nonempty (... ≅ ...)` is precisely the
  restriction isomorphism on T_V = q^{-1}(V) = X times_A V. Its second side
  applies `DerivedCategory.singleFunctor ... 0` to the ordinary pushforward
  `(Scheme.Modules.pushforward h).obj (SheafOfModules.unit ...)`, then restricts.
  In particular it does not silently replace the hypothesis by an arbitrary
  kernel or impose a derived-pushforward comparison as a hypothesis.
- `K : schemeDerivedQCohCategory X` is the full subcategory from the recorded
  definition. `K.obj` is its underlying unbounded derived object and its
  membership means all its cohomology sheaves are quasi-coherent.
- The conclusion is `Nonempty` of an actual isomorphism in D(O_V). On the left,
  `derivedPullback p`, the global derived tensor `⊗ E`, `schemeDerivedDirectImage q`
  and derived open restriction are composed in that order. On the right,
  `schemeDerivedDirectImage` is applied to
  `inv ((h ≫ p).resLE U W hWU.le) ≫ (h ≫ q).resLE V W hWV.le`, exactly j,
  and its input is the restriction of `K.obj` to U.
- The explicit common derived-category universe `w` and family of localization
  instances provide choices of derived categories, not geometric hypotheses.
  Both universes are bound explicitly; autoImplicit and relaxedAutoImplicit
  are disabled. No file-local definition, notation, or instance is introduced.

The declaration's docstring contains all six proof steps of the node: base
change of the graph, exact closed pushforward and its degree-zero realization,
localization of direct image and tensor, qcqs and quasi-coherence checks,
projection formula and composition, then cancellation across the isomorphism W→U.
The module imports the recorded modules of stated proof dependencies as the
stage-3 proof plan, separately from public statement imports.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its morphisms.
- `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `schemeDerivedCategory`, `schemeDerivedQCohCategory` and the underlying
  `schemeDerivedQCohProperty`.
- The morphism-convention node is explicitly a convention with no declaration;
  I use Mathlib's `IsSeparated`, `LocallyOfFinitePresentation`, `QuasiCompact`,
  and `QuasiSeparated`, as its record directs.
- `WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage`:
  `schemeDerivedDirectImage`; ordinary `Scheme.Modules.pushforward` and the
  degree-zero `DerivedCategory.singleFunctor` express its module input.
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist` publicly supplies
  `Proj.projectiveSpaceOverAffine` and `Proj.projectiveSpaceOverAffineToSpec`
  from `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`; their definitions are
  Proj of the total-degree homogeneous submodule and its structure morphism.
  No new projective space or twist is defined.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the fibre-product
  construction and its projections, represented by their `IsPullback` universal
  property (from Mathlib's limits API).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `WeilConjectures.AlgebraicGeometry.DerivedPullback`: `derivedPullback`.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  the global `schemeDerivedTensorMonoidal`, used by `⊗`.
- Existing helper `schemeOpenRestriction` from
  `WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps`, with its
  existing exactness instances and `Functor.mapDerivedCategory`, gives the
  standard derived restriction. Its body is exactly `overFunctor ⋙ overEquiv`
  as specified in the stage conventions. Mathlib's `Scheme.Hom.resLE` supplies
  the geometric restrictions, and `inv` uses the stated `IsIso` instance.

Edge cases checked before writing: n = 0 uses Fin 1, so P is the correct
zero-dimensional projective space; A may be the zero ring; X, Z and the opens
may be empty. Empty W forces U empty via the isomorphism, and the displayed
objects are then zero as expected. For V empty both restrictions are zero.
U and V need not be quasi-compact. E and K may be zero or unbounded. No field,
Noetherian, finite-presentation-of-h, properness-of-h beyond closed immersion,
or extra condition on E is imposed. All coordinate indices have universe u
via ULift, without restricting the ring universe.

Searches made:

- `msearch.py leanfinder`: “Derived tensor integral transform restricted to a
  closed graph equals the derived pushforward of the restricted quasi coherent
  complex”. Eight results, concerning ordinary module pullback/pushforward and
  restriction; none gives the derived graph-kernel identity.
- `msearch.py loogle`: `"FourierMukai", "derivedChow"`. No results.
- `msearch.py grep`: `Fourier.Mukai|derived.chow|chow.*transform|chowTransform`
  under Mathlib/AlgebraicGeometry. No results.
- `msearch.py leansearch`: “The derived integral transform with a graph structure
  sheaf kernel restricts to pushforward along the graph”. Eight ordinary
  pushforward/sections results, no matching derived theorem.
- Direct `rg` in `lean/WeilConjectures` and `lean/Sheaf` for
  `lemma-compute-Fourier|derived.chow|chow.*[Tt]ransform|ChowTransform`, and
  `grep -rn` for this node id in WeilConjectures: no upstream scheme match.
  The project has `AlgebraicSpace.derived_chow_transform_restriction` in
  `SpaceDerivedChowTransformRestriction`; I read its full signature and
  docstring. It uses small algebraic-space module models, an étale chart and
  a quasi-coherent kernel, and does not give this exact scheme theorem with
  unrestricted E and the specified W→U isomorphism. It is not rebound as an
  existing declaration. Exact proposed-name search in both libraries and
  `dag/lean_names_upstream.json` finds no duplicate.

Validation: the prescribed `scompile.py` compiled this file both at the sandbox
module name and its intended library module name, each in 3.8 seconds, with no
errors or unexpected warnings. Only the theorem is postponed; all data comes
from existing constructions.

## Second reading by Q03

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
