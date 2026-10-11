## Worker report

The module `Sheaf.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent` states
`AlgebraicGeometry.Scheme.exists_constructible_etaleModuleSheaf_descent` with `sorry`.
It adds no definitions, dependency modules, or nodes and does not correct the statement.
Its docstring gives all eight steps of the node's presentation-and-cokernel argument.

Hypothesis and clause correspondence:

- The directed set is `{I : Type w} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`.
  Stacks directed index sets are nonempty; the node's first proof step explicitly uses
  this. A preorder, rather than a partial order, also covers equivalent indices.
- The inverse system `(X_i, f_ii')` is `D : Iᵒᵖ ⥤ Scheme.{u}`. A morphism from
  `op i` to `op i'` represents `i' ≤ i`, with transition map `D.map f`. Identity and
  composition compatibility are part of the functor data.
- Every transition is affine through
  `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]`.
- Every stage is quasi-compact through `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`, and
  quasi-separated through `[∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]`.
  These are properties of the whole stage scheme, not of its identity morphism.
- The specified limit `X` and projections `f_i` are `(c : Cone D) (hc : IsLimit c)`:
  `X = c.pt` and `f_i = c.π.app (op i)`. No chosen limit is required, and no
  affineness or qcqs property of X is added as a hypothesis.
- The finite commutative ring is `(Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]`.
- The module sheaf on the limit is
  `F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
  This is the constant-coefficient module-sheaf encoding expressly authorized in
  `def-weil-pbc-etale-sheaves`'s `lean.note`, also used by the recorded constructibility
  predicate and the recorded inverse-image functor. It does not introduce a private
  definition of sheaves of modules or replace module sheaves by underlying set sheaves.
- Constructibility on X is `(hF : IsConstructibleEtaleModuleSheaf F)`.
- The descended index and sheaf are existentially quantified as
  `∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
- Constructibility of the descended sheaf is `IsConstructibleEtaleModuleSheaf Fᵢ`.
- The module-sheaf isomorphism is
  `Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i))).obj Fᵢ ≅ F)`.
  `Nonempty` expresses existence of an isomorphism in the same coefficient category;
  it asserts neither faithfulness nor full faithfulness of a category colimit.

Dependencies read and used:

- `def-pc-scheme`: Mathlib `AlgebraicGeometry.Scheme` and `Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`; read the locally affine locally ringed space
  structure and the scheme-morphism structure.
- `pqf-def-affine-morphism`: `AlgebraicGeometry.IsAffineHom` in
  `Mathlib.AlgebraicGeometry.Morphisms.Affine`; read its affine-open preimage field.
- `def-weil-pbc-scheme-conventions`: a convention record, with no declaration/module
  of its own. Its qcqs meanings are expressed by `CompactSpace` and
  `QuasiSeparatedSpace`, as in the project's existing affine-transition modules.
- `lem-weil-pbc-limit-affine-transition`: read
  `AlgebraicGeometry.exists_limit_affine_transition` in
  `Sheaf.AlgebraicGeometry.LimitAffineTransition`, imported here. It provides the
  existence of a limiting cone and affine projections in the node's setup. This
  statement accepts any such limiting cone instead of asserting existence again.
- `def-weil-pbc-etale-constructible-sheaf`: read and use
  `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf` from the imported
  `Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`. It quantifies over a
  finite locally closed scheme stratification with constructible parts and finite
  locally constant module-valued pullbacks, exactly as required.
- `def-weil-pbc-etale-sheaves`: read `Sheaf.AlgebraicGeometry.EtaleSheaves`, including
  its set-valued definitions, and its node's explicit authorization of the
  `Sheaf ... (ModuleCat Λ)` encoding for constructible-sheaf chapters. None of the
  set-valued predicates is used in this module, so that module is not imported.
- `def-weil-sheaf-of-modules-category`: read Mathlib `SheafOfModules` and its `Hom`
  in `Mathlib.Algebra.Category.ModuleCat.Sheaf`. The encoding chosen here is the
  authorized constant-coefficient encoding from the preceding dependency, which
  supplies exactly the signatures accepted by constructibility and inverse image.
- `def-weil-pbc-inverse-image`: read and use `AlgebraicGeometry.Etale.upperStar` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`, available transitively
  through the constructibility import. It sheafifies left Kan extension along
  etale base change and is left adjoint to direct image, with module coefficients.

Source: the local `literature/stacks-project/etale-cohomology.tex` is absent on this
machine. Read the source directly at https://stacks.math.columbia.edu/tag/09YU:
Lemma 59.73.10 assumes affine transitions and qcqs stages; (3) states the category
colimit for a Noetherian coefficient ring. Its essential-surjectivity paragraph
uses descent of etale objects and presentations; its module paragraph substitutes
095N for 09Y9. The node restricts to finite commutative coefficients, as intended;
finite commutative rings are Noetherian. The proof docstring follows the node's
expanded module argument, since Stacks omits those details.

Edge cases checked before writing:

- Empty index sets are excluded by the source's nonempty directed-set convention,
  not by an added geometric assumption. Singleton and nondiscrete directed
  preorders are allowed. `w` is independent of the scheme universe `u`, so no
  bound on the index set's universe is imposed.
- The stage schemes and the limit can be empty. No `Nonempty` instance on a scheme
  and no surjectivity assumption on transitions or projections is present.
- The zero sheaf, zero ring, and empty sums in presentations are allowed. There is
  no nontriviality or characteristic hypothesis on Λ and no nonzero-section clause.
- Coefficients and section modules use `u + 1`, exactly the universes of the recorded
  constructibility predicate and inverse-image functor. Every finite coefficient
  ring admits this universe by lifting, and constructible sheaves have finite
  locally constant values on strata. All universes and binders are explicit.
- `hc` is essential limit data even though the stage-2 proof is `sorry`; an arbitrary
  cone would not justify descent. The conclusion retains an actual module-sheaf
  isomorphism, rather than an isomorphism of underlying sets or stalk cardinalities.

Searches for an existing statement (executed via `msearch.py`; searches.jsonl records
queries and actual results):

- LeanSearch: "A constructible sheaf of modules on an inverse limit of quasi compact
  quasi separated schemes with affine transition maps descends to some stage".
  Service unavailable (Internal Server Error); no verdict inferred from this failure.
- LeanFinder: the same query returned eight results, mainly
  `AlgebraicGeometry.exists_appTop_π_eq_of_isLimit` and related global-section
  results in `Mathlib.AlgebraicGeometry.AffineTransitionLimit`, and condensed-module
  constructions. None states descent of constructible etale module sheaves.
- Loogle: `AlgebraicGeometry.Scheme, CategoryTheory.Limits.IsLimit` returned twelve
  scheme limit results, including `isAffineHom_π_app`, `Scheme.compactSpace_of_isLimit`
  and `Scheme.exists_isAffine_of_isLimit`; none is sheaf descent.
- Mathlib grep: `constructible.*(limit|descend)|(limit|descend).*constructible` returned
  zero hits.
- Project/source rg: the same pattern together with the exact node id in
  `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and `lean/Sheaf` returned
  unrelated constructible generation, immersion independence, universal-homeomorphism
  invariance, and containment of scheme-limit images in constructible subsets.
  No exact-id occurrence or matching descent theorem was found.
- Name-collision rg: `exists_constructible_etaleModuleSheaf_descent` in Mathlib,
  the source project, this project's Lean and `dag/lean_names_upstream.json` gave
  no hit.

Validation: `scompile.py F1 lem-weil-pbc-constructible-module-limit-descent` compiled
this single module on the server in 1.8 seconds, exit code 0, with no warnings.
No STATEMENT-DISPUTED flag or node fault was found.

## Second reading by F1

I independently opened the item's node and sandbox module, all eight statement
 dependency records, the two imported dependency modules, EtaleSheaves.lean,
Mathlib's Scheme, IsAffineHom and SheafOfModules declarations, and the source
Etale.upperStar and LocallyConstantDatum declarations. The original worker report
is retained above. No new definition nodes, dependency modules, or statement
correction are in this delivery, so H12/H13 and correction-citer checks do not arise.

Source reading: the local Stacks checkout is absent. I read the actual source TeX
from https://raw.githubusercontent.com/stacks/stacks-project/master/etale-cohomology.tex,
labels lemma-category-is-colimit (09YU) and lemma-category-constructible-modules
(095N), including both proofs. I also checked
https://stacks.math.columbia.edu/tag/09YU and
https://stacks.math.columbia.edu/tag/00D3. The setup of 09YU assumes qcqs stages
and affine transitions, with no field, characteristic, nonemptiness of schemes,
Noetherian scheme or surjectivity assumption. Its module clause allows a
Noetherian coefficient ring; this node explicitly specializes to finite
commutative rings, which are Noetherian. The source proof of essential
surjectivity descends a finite presentation, using descent of etale objects and
sections; 095N permits affine presentation objects. The eight-step docstring
matches the node's expanded module proof, including comparison on generators,
constructibility of the cokernel and preservation of that cokernel.

Object/hypothesis/conclusion checklist, written from the node before comparison:

1. A directed set I. Lean: `{I : Type w} [Preorder I]
   [IsDirected I (· ≤ ·)] [Nonempty I]`. Verdict: exact. Tag 00D3 defines a
   directed set to be a nonempty preorder with pairwise upper bounds, so neither
   nonemptiness nor absence of antisymmetry changes the source convention.
2. An inverse system of schemes X_i with compatible maps from larger to smaller
   indices. Lean: `(D : Iᵒᵖ ⥤ Scheme.{u})`; the stage at i is `D.obj (op i)`.
   Verdict: exact. Opposite arrows reverse the preorder and functoriality imposes
   identities and compositions. Mathlib Scheme is locally affine locally ringed
   space data and Hom is a morphism of those spaces, as the dependency requires.
3. Affine transitions. Lean: `[∀ {i j : Iᵒᵖ} (f : i ⟶ j),
   IsAffineHom (D.map f)]`. Verdict: exact. I read the field
   `isAffine_preimage`: every affine open has affine preimage. Identity arrows
   add no constraint because isomorphisms are affine.
4. Every stage quasi-compact. Lean: `[∀ i : Iᵒᵖ,
   CompactSpace (D.obj i)]`. Verdict: exact, a property of the underlying scheme
   space, not the automatically quasi-compact identity morphism.
5. Every stage quasi-separated. Lean: `[∀ i : Iᵒᵖ,
   QuasiSeparatedSpace (D.obj i)]`. Verdict: exact, as in the scheme conventions.
6. Limit X with the specified projections f_i. Lean: `(c : Cone D)
   (hc : IsLimit c)`, with X = `c.pt` and f_i = `c.π.app (op i)`.
   Verdict: exact. Arbitrary specified limiting cones are allowed; no extra
   affine-projection hypothesis is assumed. The recorded dependency
   `exists_limit_affine_transition` constructs such limits and affine projections;
   this statement does not need to choose its particular cone. Its same-universe
   restriction on indices is not imposed on the present theorem.
7. A finite commutative ring Λ. Lean: `(Λ : Type (u + 1)) [CommRing Λ]
   [Finite Λ]`. Verdict: exact, with the recorded coefficient convention. No
   nontriviality, field or characteristic assumption is added.
8. A sheaf F of Λ-modules on the small etale site of X. Lean:
   `(F : Sheaf c.pt.smallEtaleTopology (ModuleCat.{u + 1} Λ))`.
   Verdict: exact under the explicit two-encoding decision in the
   def-weil-pbc-etale-sheaves lean.note. The general SheafOfModules dependency is
   over a constant ring sheaf; the authorized constant-coefficient encoding here
   retains linear morphisms and is accepted by the recorded inverse image.
9. F is constructible. Lean: `(hF : IsConstructibleEtaleModuleSheaf F)`.
   Verdict: exact. I opened the definition: a finite locally closed scheme
   stratification, constructible strata, and etale-local module-sheaf
   isomorphisms to finite constant module values after inverse image. Its
   LocallyClosedStratification records the immersed schemes and their images;
   LocallyConstantDatum supplies the trivializing etale cover. This is the node's
   predicate, not the source's alternative geometric-stalk formulation.
10. There exists an index i, then a sheaf F_i on that stage, with the same ring.
    Lean: `∃ (i : I) (Fᵢ : Sheaf (D.obj (op i)).smallEtaleTopology
    (ModuleCat.{u + 1} Λ))`. Verdict: exact quantifier order and coefficient ring.
11. F_i is constructible. Lean: `IsConstructibleEtaleModuleSheaf Fᵢ`.
    Verdict: exact, using the same recorded predicate as for F.
12. There exists a Λ-module-sheaf isomorphism f_i^{-1}F_i ≅ F. Lean:
    `Nonempty ((Etale.upperStar (ModuleCat.{u + 1} Λ)
    (c.π.app (op i))).obj Fᵢ ≅ F)`. Verdict: exact. The source upperStar is
    sheafified left Kan extension along etale base change, left adjoint to
    lowerStar. No exactness or adjunction instance is added as a hypothesis.
    This concludes essential surjectivity only, without asserting full faithfulness.

Edge cases: the empty index set is outside the source's directed-set definition;
singleton indices and preorders with equivalent distinct indices are admitted.
Empty schemes at any stage and an empty limit are admitted. The zero coefficient
ring, zero sheaf and presentations with zero generators/relations are admitted;
there is no nonzero object hypothesis. No n or characteristic parameter is
restricted. Scheme universe u and index universe w are independently bound.
Modules and coefficients use u + 1 exactly as their recorded dependencies do;
finite rings can be represented in that universe, and a larger ambient universe
can always be chosen. No variable or universe is implicitly unbound.

Independent searches (in addition to the worker's searches):

- LeanSearch via msearch.py: "Every constructible etale sheaf of modules over a
  finite ring on an inverse limit of qcqs schemes with affine transition
  morphisms is inverse image of a constructible module sheaf at a stage".
  Service returned Internal Server Error; no no-match verdict inferred.
- LeanFinder via msearch.py: "Essential surjectivity for finite coefficient etale
  module sheaves under inverse limits of schemes with affine morphisms".
  Eight hits concern standard etale algebras, composition of etale morphisms,
  etale over-category forgetful functors and essential surjectivity of Spec.
  Their displayed signatures do not state the item.
- LeanFinder via msearch.py: "A locally constant finite module sheaf on a
  projective limit of schemes is pulled back from one of the schemes".
  Eight hits concern condensed module constructions and locally constant
  functions on profinite limits. Their signatures concern functions/topological
  spaces, not constructible etale module sheaves on schemes.
- Loogle via msearch.py: `Sheaf, ModuleCat` could not resolve `Sheaf`;
  this is not evidence of absence.
- Independent rg over all Mathlib, WeilConjectures and this project's lean/Sheaf
  used `(constructible|locallyconstant|locally_constant).*(descen|islimit|inverse.limit)`
  and the reverse order. The relevant nearby source theorem is
  `Etale.exists_isNoetherian_upperStar_iso` in ConstructibleSheaf/FinitePushforward.lean,
  which I opened: it produces some Noetherian scheme and morphism, not a stage
  of a prescribed inverse system. Refinement and UniversalHomeomorphism concern
  local constancy along special morphisms. None duplicates this item.
- Broader site/sheaf/descent/limit rg and the exact declaration-name/node-id search
  over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json found no matching
  theorem or name collision. Mathlib's profinite locally constant function
  descent and condensed colimit results have different objects and conclusions.

Mismatch and repair: no mathematical or metadata mismatch was found. I removed
`import Sheaf.AlgebraicGeometry.LimitAffineTransition`: no declaration from that
module is used in the signature, and its theorem is needed only for the future
proof. The remaining constructibility import already supplies all types and
instances used. The worker report's statement that both modules are imported
therefore describes its original version. No declaration, binder, conclusion,
node field, or proof docstring was rewritten.

Validation: scompile.py compiled the final single module on the server in 1.8 s,
exit code 0, with no warnings. I mechanically compared the complete theorem
signature before `:= by` with lean.statement: verbatim equal. All lines are at
most 100 characters. The only theorem proof is `sorry`; no definition is added.

## Reviewer fix (R-cml1134)

The index set was bound in an independent universe (`{I : Type w}`, `universe w u`).
That reading is false for w above u (the same fault found in C1 02bc80ff3 and
G1 117cfd333: a large directed system of u-small schemes, e.g. a strictly increasing
chain of u-small fields, has a limit cone whose descent to a stage fails), and it departs
from the recorded form of lem-weil-pbc-limit-affine-transition
(`exists_limit_affine_transition`, `{I : Type u}`). The index is now `{I : Type u}`,
the schemes' universe, and `universe w` is removed. The statements in the worker report
and the second reading that `w` is independent are superseded. Nothing else changed.
