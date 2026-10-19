## Worker report

The module `Sheaf.AlgebraicGeometry.OpenDegreeZeroConstructible` states
`AlgebraicGeometry.Scheme.isConstructibleEtaleModuleSheaf_lowerStar_of_openImmersion_over_field`.
Its entire proof is `sorry`; no definitions, auxiliary theorems, or proofs are added.
The node changes only in `lean`. Its source statement and all four proof paragraphs were read
in the blueprint file `sec-smooth-purity/sk-prop-a1-kummer/thm-fin-open-degree-zero.md`.
The declaration docstring records the DAG's expanded four-step induction plan, including the
unit compatibility, finite product, and direct-image composition arguments.

Hypotheses and conclusion, clause by clause:

- “over a field”: `{k : Type u} [Field k]`, with the structure map specified by
  `[X.Over (Spec (.of k))]`. This follows the project's scheme-over-base convention.
- “X of finite type”: `{X U : Scheme.{u}}` with
  `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`; together these are precisely finite type.
  The conventions node fixes no new declaration; these are its Mathlib notions.
- “j : U ↪ X an open immersion”: `(j : U ⟶ X) [IsOpenImmersion j]`.
  The node gives no separate structure morphism for U, so none is required.
- “finite commutative ring”: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
  This is the established coefficient universe for etale `ModuleCat` sheaves.
- “module sheaf on U_et”: `(F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
  ModuleCat-valued sheaves are the project's encoding of modules over the constant ring sheaf.
- “F constructible”: `(hF : IsConstructibleEtaleModuleSheaf F)`, using the recorded finite
  locally closed constructible stratification with finite constant module values.
- “j_*F constructible on X_et”:
  `IsConstructibleEtaleModuleSheaf ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F)`.
  The target site is X.smallEtaleTopology by the signature of lowerStar.

Dependency declarations used:

- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`; and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `AlgebraicGeometry.QuasiCompact`.
  These render the conventions node's finite-type clause directly.
- `Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion`:
  `AlgebraicGeometry.IsOpenImmersion`, rendering that convention directly.
- `Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes`, the recorded module of
  `def-weil-pbc-constructible-complexes`, publicly imports
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf` and its declaration
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`, used here for the sheaf clause.
  Its recorded `Etale.DerivedCategory.isBoundedConstructible` is the complex clause and is
  intentionally not applied to this degree-zero sheaf statement.
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `AlgebraicGeometry.Etale.lowerStar`, whose full signature and docstring were read.
  It takes the coefficient abelian category and the scheme morphism, and evaluates by
  precomposition with etale base change, exactly the direct-image formula in the node.

Every proof dependency with a recorded module is imported without `public` unless already a
statement import. The mathlib proof leaves are covered by imports of Noetherian and Finite.
`lem-kun-open-immersion-restriction` has no recorded declaration, so no module import can yet
be added; it is cited in the proof docstring and is not needed to type this statement.

Edge cases checked: X and U may be empty, U may equal X (identity immersion), U may be
nondense or disconnected, X may be nonreduced or reducible and need not be separated or
normal, F may be zero, and Λ may be the zero ring. There is no nonempty, integrality,
normality, separatedness, or independent finite-type hypothesis on U. All characteristics,
including coefficients in the characteristic of k, are admitted. The theorem is degree
zero, so no invertibility assumption on the coefficient ring is present. Universe u is
explicit, and Λ and its modules use the existing u+1 convention; no independent test-universe
restriction is imposed. All variables and universes are bound explicitly.

Searches for an existing theorem:

- `msearch.py leanfinder`: “The direct image of a constructible etale sheaf of finite modules
  along an open immersion into a scheme of finite type over a field is constructible”. Eight
  hits concern constructibility of images/preimages of subsets, not direct images of sheaves.
- `msearch.py loogle`: `"Sheaf", "constructible"`; valid query, zero hits.
- `msearch.py grep`: `constructible.*lowerStar|lowerStar.*constructible|IsConstructibleEtaleModuleSheaf`;
  Mathlib root, zero hits.
- `msearch.py leansearch`: “constructibility of the direct image of a constructible etale
  module sheaf along an open immersion over a field”; unavailable (Internal Server Error).
  No absence conclusion is drawn from this service failure.
- `rg` in WeilConjectures and lean/Sheaf for constructibility/lowerStar/open: finite and finite
  etale pushforward statements, the normal-open lisse special case, lowerShriek preservation,
  and derived prime-field finiteness theorems were found. None states this theorem for arbitrary
  constructible finite-ring sheaves and arbitrary open immersions into finite-type k-schemes.
- `rg` for `thm-fin-open-degree-zero` in WeilConjectures: no hits. `rg` for the proposed
  declaration name in both source roots: no hits. The source and project definitions are
  reused, without a second constructibility predicate or direct-image construction.

No statement dispute, correction, new node, or dependency repair is needed.

Validation: `scompile.py Q09 thm-fin-open-degree-zero` compiled the delivered module
cleanly (exit 0, no warnings or errors), including the sandbox and final module checks.
The metadata signature matches the source verbatim; every Lean line is at most 100 characters.

## Second reading by Q09

I independently opened the sandbox node and Lean file, the three statement-dependency
records and their source declarations, and the original blueprint statement and all four
proof paragraphs. The blueprint and Stacks sources absent from the shared clone were read
from the read-only literature mirror in work-bp/sheaf. The node's source is this blueprint
node, rather than a Stacks theorem with additional standing hypotheses. Its statement
explicitly quantifies over a field and an arbitrary finite commutative coefficient ring.
I also read its enclosing unit and chapter, and Stacks etale-cohomology.tex at Tags 03RU,
095E, 03RZ and 095Q. Their module assertions use a Noetherian ring, which a finite ring
already supplies; their qcqs assumptions are available here because finite type over a
field makes X Noetherian, as are its opens. They require no separatedness or invertibility
hypothesis for this degree-zero assertion.

The node's object/hypothesis/conclusion checklist and its Lean rendering are:

1. Base field k: `{k : Type u} [Field k]`. Exact; neither algebraic closure nor perfection
   is assumed, and all characteristics occur.
2. Ambient scheme X over k: `{X U : Scheme.{u}} [X.Over (Spec (.of k))]`. Exact;
   `X ↘ Spec (.of k)` is the structure map in the project's recorded convention.
3. Finite type of X over k: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` together with
   `[QuasiCompact (X ↘ Spec (.of k))]`. Exact; I read the classes in Mathlib's
   Morphisms/FiniteType and Morphisms/QuasiCompact and the conventions node's explicit
   equivalence with finite type. No separate Noetherian or separated assumption appears.
4. Open subscheme and its morphism: `(j : U ⟶ X) [IsOpenImmersion j]`. Exact; Mathlib's
   IsOpenImmersion is the scheme open-immersion property. No density, nonemptiness,
   normality, irreducibility, or separately chosen incompatible k-structure on U is assumed.
   The composite of j with X's structure map gives U its k-structure when needed.
5. Finite commutative coefficient ring: `{Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]`.
   Exact; this is a ring, not necessarily a field or a nonzero ring. There is no
   coefficient-order invertibility condition or restriction relative to char(k).
6. Sheaf F on the small etale site of U with these coefficients:
   `(F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ))`. Exact; the constant-ring
   module encoding is the one used by the dependency, not structure-sheaf modules.
7. Constructibility of F: `(hF : IsConstructibleEtaleModuleSheaf F)`. Exact; opening
   BoundedConstructibleComplexes and its public import IsConstructibleEtaleModuleSheaf
   shows a finite `LocallyClosedStratification`, constructible parts, and etale local
   isomorphisms to constant sheaves with finite module values. Opening
   LocallyClosedStratification confirms scheme immersions realizing the parts. Thus this
   is the sheaf clause of def-weil-pbc-constructible-complexes, not its derived-complex
   predicate and not the upstream predicate with a different finite-generation interface.
8. Conclusion: `IsConstructibleEtaleModuleSheaf
   ((Etale.lowerStar (ModuleCat.{u + 1} Λ) j).obj F)`. Exact, and the only conclusion.
   I read lowerStar in SixFunctors/Etale/UpperLowerStar/Defs, including the preceding
   coefficient assumptions and the following object/restriction formulas. It is
   precomposition with etale base change, with `(j_*F)(T) = F(T ×_X U)` and restriction
   along the base-changed arrow. Its target is sheaves on X.smallEtaleTopology, with the
   same coefficients. It is the module direct image in def-weil-pbc-direct-image.

Every object is universally quantified before the relevant hypotheses and conclusion.
The implicit k, X, U and coefficient binders do not introduce an existential choice.
The Scheme.{u} and ModuleCat.{u+1} universes follow the actual dependency signatures and
small-etale-site size convention. There is no independent too-small universe for tests,
no equality of distinct site universes, and no extra explicit typeclass hypothesis.

Edge cases: the empty ambient scheme (hence empty U), empty U in nonempty X, the identity
open immersion, nondense and disconnected opens, reducible and nonreduced X, nonseparated
finite-type X, the zero sheaf, and the zero coefficient ring are all admitted. The finite
stratification definition permits an empty index set. There is no index or n in the
signature; this is ordinary degree-zero direct image, so n = 0 needs no added bound or
positive-degree assumption. Coefficients in the characteristic of k remain admitted.

Independent searches, using words beyond the first worker's query:

- LeanFinder: `extension of constructible torsion module sheaves by direct image of an
  open subscheme over a field`. Eight hits concerned Tilde sections, module restrictions,
  sheaf conditions, and qcqs section identities; none states this sheaf theorem.
- Loogle: `"Sheaf", "lowerStar"`. Zero hits, with no parser or identifier error.
- LeanSearch: `open immersion direct image finite etale sheaf constructible arbitrary
  field`. The service returned Internal Server Error. This gives no absence evidence.
- msearch grep of all Mathlib: `constructible.*(sheaf|pushforward)|
  (sheaf|pushforward).*constructible` (one regex without the line break). Zero hits.
- Direct rg in Mathlib's Sites and AlgebraicGeometry, upstream WeilConjectures, and
  project lean/Sheaf for constructibility with pushforward, direct image, and lowerStar,
  plus the node id and proposed declaration name. I opened the candidate
  RealSheaves/Boundary.isConstructibleSheaf_lowerStar: it assumes a curve, finite boundary,
  and a finite locally constant sheaf, and concludes for middleExtension with the upstream
  constructibility predicate. It is not this statement. I opened NormalOpenLisseImage:
  integral ambient and normal open with lisse input are a special case. The finite and
  finite-etale pushforward results concern different morphisms. I also opened
  OpenDirectImageFiniteCoefficients and FiniteTypeDirectImageConstructibility: their
  bounded derived conclusions impose allowable coefficients invertible on the base,
  excluding cases this theorem covers. No exact existing declaration was found.
- The proposed full name and node id have no declaration collision in upstream sources,
  project Lean, or dag/lean_names_upstream.json. The existing dependency notions are reused.

No mathematical mismatch, missing notion, new node, dependency repair, or statement
correction was found. I left the correct Lean and node unchanged and added this independent
reading to the report. H5/H6: the file contains one theorem, its proof exactly `by sorry`,
and no definitions, hidden assumptions, or additional proved assertions. H8: the module
and theorem docstrings cite the source and blueprint id; the theorem follows the node's
four proof steps, including reduction and reflection, the generic normal opens and finite
product, the supported kernel and stalk-unit calculation, and the final image/extension.
H9: the namespace and imports follow the conventions, all universes and variables are
explicitly bound, and no line exceeds 100 characters. The lean.statement string matches
the theorem signature verbatim. The only node field differing from the shared base is lean.

Second-reader validation: scompile.py compiled this delivered module in both sandbox and
library-module modes with exit 0 and no errors or warnings (including the final module
check under the default 60-second limit). The independent reading makes no proof claim;
the named theorem remains postponed exactly as required for stage 2.
