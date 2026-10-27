## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceInvariantOpenQuotient` states
`AlgebraicGeometry.AlgebraicSpace.space_invariant_open_quotient`, with one `sorry` and
no additional definitions or axioms. The DAG statement, dependencies, and proof are unchanged.
The source is the inverse construction in Stacks, Properties of Spaces, Tag 03BZ,
`lemma-open-subspaces`, read in `literature/stacks-project/spaces-properties.tex`, lines
491–504. The quotient inputs were checked against Spaces Tags 0262, 02WT, 02WW and 02WU.
No statement dispute or unusable dependency record was found.

Hypotheses and clauses, in node order:

| Node text | Lean rendering |
| --- | --- |
| Scheme S and algebraic space X over S | `{S : Scheme.{u}} (X : AlgebraicSpace S)` |
| Representable surjective étale scheme atlas | `(U : Over S) (p : yoneda.obj U ⟶ X.obj.obj)`, `hp : IsEtale p`, `hsur : IsSurjective p`. Both predicates include scheme-test representability. |
| Field-valued classes with atlas topology | `Point X.obj.obj` and its existing `pointTopologicalSpace` instance; no new point model. |
| Any open subset O | `(O : Set (Point X.obj.obj)) (hO : IsOpen O)` |
| R = U ×_X U, with projections s,t | `(R : Over S) (s t : R ⟶ U)` and `hR : IsPullback (yoneda.map s) (yoneda.map t) p p`. This supplies an arbitrary representative, as in the recorded atlas-presentation theorem, rather than presuming a choice of representing scheme. |
| V is the open subscheme with underlying set preimage of O | `∃ (V : Over S) (i : V ⟶ U), IsOpenImmersion i.left ∧ Set.range i.left.base = schemePointMap p ⁻¹' O`. An open immersion with this image is precisely that open subscheme, up to its canonical isomorphism over U. In particular this asserts that the preimage is open instead of assuming it. |
| R_V is the double restriction; s⁻¹(V)=t⁻¹(V)=R_V as open subschemes of R | `∃ (RV : Over S) (r : RV ⟶ R) (sV tV : RV ⟶ V), IsPullback r sV s i ∧ IsPullback r tV t i`. The SAME map r represents both pullbacks, so their scheme structures as well as their images agree. Because i is mono, the common pullback also represents the double restriction: for two V-endpoints and an R-section, the two factorizations to RV agree by monicity of r. Thus this is a representative-independent rendering of the stated equality, not merely equality of underlying sets. |
| Restricted projections form an étale equivalence relation | `Mono (prod.lift sV tV)`, `∀ T, Equivalence (fun a b ↦ ∃ v : T ⟶ RV, v ≫ sV = a ∧ v ≫ tV = b)`, `Etale sV.left`, `Etale tV.left`. |
| J = V/R_V is the fppf sheaf quotient | Existential `J : Sheaf (Scheme.fppfTopology.over S) (Type u)` and `η : coequalizer (yoneda.map sV) (yoneda.map tV) ⟶ J.obj`; precomposition by η is bijective on maps to EVERY fppf sheaf G. This is exactly the sheafification universal property at the presheaf relation quotient. Existence is in the conclusion, with no blanket HasWeakSheafify assumption. |
| J is an algebraic space | `IsAlgebraicSpace J` |
| h_V → J is representable surjective étale | `IsEtale (coequalizer.π ... ≫ η)` and `IsSurjective (coequalizer.π ... ≫ η)` |
| The induced map j:J→X | Existential `j : J.obj ⟶ X.obj.obj` with `(coequalizer.π ... ≫ η) ≫ j = yoneda.map i ≫ p`. The quotient universal property makes this the canonical induced map; it is not an unrelated map. |
| j representable by open immersions | `IsRepresentableWith (fun _ _ f ↦ IsOpenImmersion f.left) j` |
| Its point image is O | `pointImage j = O` |
| Identifying J with its image gives an open subspace | `IsIso (Subfunctor.toRange j)` and `∃ A : OpenSubspace X, A.val = Subfunctor.range j`. The existing canonical map to the range is the identification. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: `pointTopologicalSpace`, `pointImage`;
  its public point-classes dependency supplies `Point` and `schemePointMap`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceOpenSubspace`: `OpenSubspace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`, `etale_fibreProduct_isScheme`;
  imported as required for the statement's fibre-product dependency.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion`.
- `Mathlib.CategoryTheory.Sites.Sheafification`: `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`. The statement uses their defining universal property at
  the particular presheaf, as do the recorded quotient and atlas-presentation interfaces.
- `Mathlib.AlgebraicGeometry.Sites.Fpqc`: `Scheme.fppfTopology`, with
  `GrothendieckTopology.over` from `Mathlib.CategoryTheory.Sites.Over` (publicly available
  through the algebraic-space dependencies).
- `Mathlib.CategoryTheory.Subfunctor.Image` (public through OpenSubspace):
  `Subfunctor.range`, `Subfunctor.toRange` and its existing mono-to-isomorphism instance.

The modules of the stated proof dependencies are imported without `public`:
`EtaleAtlasPresentation` (`etale_atlas_presentation`),
`EtaleRelationRestrictionQuotient` (`restrictedEtaleRelation`, its two projections,
`etale_relation_restriction_quotient`), `EtaleRelationQuotient`
(`relationQuotientMap`, `etale_relation_quotient`), `EtaleRelationFindingOpens`
(`etale_relation_finding_opens`), `Mathlib.AlgebraicGeometry.Restrict`
(`isPullback_morphismRestrict`), and `Mathlib.AlgebraicGeometry.Morphisms.Etale`
(`Etale` and the open-immersion-to-étale instance).
The remaining proof node `lem-a1-space-point-open-calculus` has no Lean record in
this read snapshot, so it has no recorded module to import; its only use here is
point-surjectivity of the atlas, as recorded in the proof docstring. It supplies no
notion needed to type this statement. No downstream open-image/order-isomorphism module
is imported, avoiding a circular proof route.

Edge cases checked before writing: O empty gives the empty V and empty quotient; O all
of |X| gives V isomorphic to U and J isomorphic to X. The empty algebraic space and empty
atlas require no nonemptiness assumptions. The identity atlas of a scheme gives its
usual open subscheme. A disconnected or non-quasi-compact atlas is allowed: no affine,
finite-type, quasi-separated or quasi-compact hypothesis occurs. All objects and tests
use the recorded universe u; the existing Point type is in u+1. The theorem has
`set_option autoImplicit false` and explicitly binds the sole universe u and all variables.

Searches performed using the prescribed msearch.py wrapper:

- LeanFinder: "Restriction of an etale equivalence relation to an invariant open
  subscheme gives an open immersion of fppf sheaf quotients" — 8 hits, only scheme
  gluing/open-immersion results; no matching algebraic-space theorem.
- Loogle: `"AlgebraicSpace", "quotient"` — 0 hits.
- Grep Mathlib AlgebraicGeometry: `AlgebraicSpace|invariant.*open.*quotient` — 0 hits.
- LeanSearch: "The quotient of an etale equivalence relation restricted to an invariant
  open subscheme is an open algebraic subspace with the prescribed point image" — 8
  hits on scheme restriction, discrete quotients and unrelated colimits; no match.
- `rg` of `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json` for
  `invariantOpen|invariant_open|invariant.*quotient|OpenSubspace` and the item id:
  only generic relation restrictions, open-chart descent, existing open-subspace
  primitives and unrelated invariant constructions. `space_invariant_open_quotient`
  occurs in none of these sources. The existing open-subspace correspondence does not
  supply the restricted relation, quotient atlas or the invariant-open construction,
  and is a consumer of that construction. The open-chart descent theorem likewise
  does not assert this node's full quotient construction.
- Read the full signatures/docstrings of the recorded statement dependencies and the
  quotient/atlas proof interfaces. No new notion or dependency repair was necessary.

Validation: scompile.py compiled this single delivered file in sandbox mode (3.9 s) and
library mode (5.7 s), with no errors or warnings. The only proof body is `by sorry`;
maximum source line length is 91 characters. The node's Lean signature was extracted
verbatim from the theorem keyword through its final type, and JSON was written with
indent 1, Unicode preserved, and a final newline.

## Second reading by Q72

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
