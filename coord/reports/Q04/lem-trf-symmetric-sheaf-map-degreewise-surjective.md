## Worker report

The delivery states `AlgebraicGeometry.SymmetricAlgebraSheaf.exists_map_degreewise_locallySurjective`
in `Sheaf.AlgebraicGeometry.SymmetricSheafMapDegreewiseSurjective`, with its whole proof
`sorry`. It adds the real definition `IsHomogeneousSection` in the separate module
`Sheaf.AlgebraicGeometry.SymmetricHomogeneousSections`. No theorem is proved and no
existing statement is corrected. The item gains only its Lean record and the new
definition dependency.

Hypothesis and clause audit, with `AlgebraicGeometry.SymmetricAlgebraSheaf` open:

- A scheme S: `{X : Scheme.{u}}`, with arbitrary explicitly declared universe `u`.
- Quasi-coherent O_S-modules F and E: `(F E : X.Modules)` and the two instances
  `[F.IsQuasicoherent] [E.IsQuasicoherent]`. Finite type and coherence are not assumed.
- An O_S-linear morphism: `(u : F ⟶ E)`, using the existing category of module sheaves.
- Surjectivity as a sheaf map, rather than on each open's sections:
  `[PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) u.val]`.
  Mathlib defines this as local surjectivity of the underlying abelian-group presheaf
  map. On the open-cover topology its image sieve covers each section's domain,
  exactly the stipulated open covering with module-section lifts.
- The specified symmetric algebra sheaves and degree-one maps are the existing
  `algebra F`, `algebra E`, `inclusion F`, and `inclusion E`; none is chosen anew.
- The induced algebra-sheaf morphism is `∃ a : algebra F ⟶ algebra E`. This is a
  morphism under the structure sheaf, not a free parameter supplied as a hypothesis.
- The first conjunct gives the generator equation for every open U and section x:
  `a.right.hom.app (op U) ((inclusion F).val.app (op U) x) =
  (inclusion E).val.app (op U) (u.val.app (op U) x)`.
- Uniqueness is asserted against every algebra-sheaf map b satisfying only that
  generator equation, with conclusion `b = a`. Thus uniqueness is not restricted
  to maps already satisfying the grading or surjectivity conclusions.
- Preservation of every degree is the third conjunct, for all `n : ℕ`, all opens U,
  and homogeneous sections s: `IsHomogeneousSection F n U s` implies
  `IsHomogeneousSection E n U (a.right.hom.app (op U) s)`.
- Identity in degree zero is the fourth conjunct: each scalar r under the canonical
  O_X-to-Sym(F) structure map is sent to the same scalar under O_X-to-Sym(E).
  The canonical grading has degree zero R·1, as in the recorded grading theorem.
  This is precisely the identity after identifying both degree-zero sheaves with O_X.
- Degreewise sheaf surjectivity is the last conjunct. For every `n : ℕ`, every open U
  and homogeneous t it provides an index type I, opens `V : I → X.Opens`, inclusions
  `hV : ∀ i, V i ≤ U`, and `iSup V = U`, followed by sections v_i in Sym(F)(V_i).
  Each v_i is homogeneous of the same degree n, and the final equation identifies its
  image with `(algebra E).right.obj.map (homOfLE (hV i)).op t`, exactly t restricted.
  The cover index lives in `Type u`, sufficient because a cover can be chosen indexed
  by points of U (also in `Type u`); this does not restrict the schemes or local lifts.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its Hom category.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`: the recorded public
  `SheafOfModules.IsQuasicoherent` interface (its Mathlib definition is in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`). The node records the
  finite-type conjunction as its primary name, but explicitly exposes quasi-coherence
  among its declarations; that exact predicate is used, not the conjunction.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, a
  transparent abbreviation for `SheafOfModules`. Scheme.Modules is the existing
  specialization of this category, with Mathlib's linear morphisms and restrictions.
- `Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebra`:
  `AlgebraicGeometry.exists_quasiCoherentSymmetricAlgebra`, the universal property and
  affine comparison for the canonical construction. Its full signature and proof
  docstring were read; the proof of the new theorem is planned on these inputs.
- `Sheaf.AlgebraicGeometry.SymmetricAlgebraSheafConstruction`:
  `algebra`, `sections`, `sectionMap`, `inclusion`, with their actual sheafification data.
- `WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded`:
  `SymmetricAlgebra.graded_by_tensor_images`, including the pure-product span,
  degree-zero and degree-one descriptions and internality.
- `Sheaf.AlgebraicGeometry.CanonicalSymmetricGradedAlgebra`:
  `gradedAlgebraData`, whose `grading V n` is exactly the nth power of the range of
  the degree-one inclusion on V. Its full construction and restriction theorems
  were read. It is used through the new definition node.
- `Mathlib.AlgebraicGeometry.AffineScheme`: `Scheme.isBasis_affineOpens`, the recorded
  proof dependency, imported as a proof import and read with its signature.

The existing symmetric-algebra existential theorem has the canonical algebra and
inclusion as explicit witnesses in its implementation. The delivery uses those
actual constructions rather than replacing them with arbitrary algebras/maps.

Edge cases checked mathematically before writing:

- n = 0 is included in every `n : ℕ` quantifier; the scalar identity supplies its lift.
- n = 1 recovers local lifting of module sections; zero source/target modules remain
  permitted. Surjectivity of 0 → E forces E = 0, while the degree-zero map remains O_X.
- An empty domain or empty scheme admits the empty covering (`I` empty); no Nonempty
  hypothesis occurs, and the homogeneous-section definition has the expected
  vacuous affine tests on the empty domain.
- Empty finite sums lift by zero. No positive rank, finite generation, characteristic,
  noetherianity, affine global base, or quasi-compactness assumption is introduced.
- On a non-quasi-compact open, membership is checked on every affine subopen. It does
  not require a single global finite polynomial expression, which would be too strong.
- On an affine U the test V = U and the canonical affine section isomorphism give
  exactly the existing symmetric degree. Conversely restriction preserves the grades.
  Since affine opens form a basis, these tests describe the degree subsheaf on every U.

Searches for existing statements/notions (all through the prescribed wrapper when applicable):

- LeanFinder: “A locally surjective morphism of quasi-coherent module sheaves induces
  a graded morphism of symmetric algebra sheaves surjective in each degree”: eight
  hits, including `PresheafOfModules.IsLocallySurjective`,
  `SymmetricAlgebra.algHom_surjective` and `SymAlg.sym_surjective`. None is the
  symmetric-power sheaf result; the first supplies the hypothesis predicate.
- Loogle: `SymmetricAlgebra.lift, Function.Surjective`: zero hits.
- Mathlib grep wrapper: `SymmetricAlgebra.*surjective|symmetric.*[Ss]heaf|symmetricDegree`:
  four hits in monoidal-category files; no exact statement.
- LeanSearch: “Homogeneous degree n sections of the symmetric algebra sheaf on a scheme
  are detected on affine open subsets”: eight hits involving absolute Proj fraction
  sections and affine-open geometry, not homogeneous sections of Sym(F).
- LeanFinder: “Homogeneous degree n sections of a quasi coherent symmetric algebra sheaf
  are the sections whose restrictions to every affine open lie in the nth power of the
  degree one image”: eight hits, all Proj/fraction-section constructions, no match.
- Mathlib grep wrapper in AlgebraicGeometry: `homogeneous.*section|symmetricDegreeSections|IsHomogeneousSection`:
  one hit in the absolute Proj structure sheaf; it does not define this notion.
- Direct rg over Mathlib, lean/WeilConjectures and lean/Sheaf for
  `isHomogeneousSection|homogeneousSections|degreeSections|symmetricDegreeSections|SymmetricAlgebraSheaf.map`:
  no matching declarations. Broader symmetric-algebra searches found the canonical
  construction, affine grading and ring-level quotient results, all reused as applicable.
- Direct rg for the item id in lean/WeilConjectures: no match.
- DAG content search and `tools/blueprint_refs.py search symmetric` (72 blueprint hits)
  found the existing canonical affine graded algebra but no arbitrary-open homogeneous
  section predicate. `blueprint_refs.py ancestor` identified lem-trf-local-term-locality.

Sources opened: literature/stacks-project/modules.tex, Section 01CF and the local-tensor
algebra and presentation-sym-exterior lemmas (01CG and 01CJ); the current blueprint's
lem-trf-local-term-locality proof, and the recorded DAG proof. No statement dispute,
source correction, or unusable dependency interface was found.

Validation: both delivered modules are checked separately in dependency order by
scompile.py; only the main theorem has a postponed proof. Final dry-run results are
recorded below after validation.

## New nodes

`def-trf-symmetric-homogeneous-sections` defines the missing membership predicate
`IsHomogeneousSection F n U s` on the actual symmetric algebra sheaf. It requires,
for each affine V ⊆ U, an element of `(gradedAlgebraData F).grading V n` mapping to
s|_V under `sectionMap`. All data is a concrete formula; there is no choice and no
sorry. Its source is Section 01CF and Tag 01CG, using the existing quasi-coherent
affine section comparison. The searches listed above exclude existing general-open
homogeneous membership nodes/declarations. The canonical affine graded algebra
supplies grades only on affine opens, so its notion is reused rather than duplicated.
The new node cites the scheme, quasi-coherent module, module category, canonical
symmetric sheaf construction, affine comparison and affine grading nodes.

## Second reading by Q04

A separate clause-by-clause reread in this single dispatcher-worker session compared
the original JSON with both completed files. The scheme, quasi-coherent assumptions,
linear map and local surjectivity are present; the conclusion separately gives the
canonical generator equation, uniqueness among all extensions, every-degree
preservation, scalar identity and every-degree covering lifts. The degree definition
uses the existing affine grade via the canonical section map, with all affine
subopens quantified. In particular it introduces neither sectionwise surjectivity
nor finite generation. Empty coverings and degree zero remain included. The reread
found a namespace spelling error for the open-cover topology during compilation;
the definition in Mathlib/CategoryTheory/Sites/Spaces.lean is in the root `Opens`
namespace, and the signature/record now use that name. No mathematical mismatch
required a statement change. No independent agent was started, as the dispatcher
brief forbids it; the maintainer's independent review is external to this worker.

Final validation: scompile.py compiled both modules cleanly, including their library
module paths. deliver2.py --no-push returned `OK (dry run)` at d4bd099cf84, with
preflight and per-file compiles passing. The delivery contains the two Lean modules,
the item node, the new definition node and this report only.
