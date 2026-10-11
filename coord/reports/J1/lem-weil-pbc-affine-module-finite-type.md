## Worker report

The module `Sheaf.AlgebraicGeometry.AffineModuleFiniteType` states
`AlgebraicGeometry.Scheme.Modules.affine_module_finite_type`, with one named theorem
and its proof `sorry`. No definition is added, no node statement is changed.

Hypothesis and clause correspondence:

- Schemes U and X: `{U X : Scheme.{u}}`; the given morphism u is `(f : U ⟶ X)`.
- Affineness: `[IsAffineHom f]`, exactly inverse images of affine opens being affine.
- A = u_* O_U: local notation `A` is
  `(TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj U.sheaf`.
  `AR` forgets commutativity into RingCat using `sheafCompose`; this does not change
  the underlying sheaf or ring action.
- An A-module M: `(M : SheafOfModules.{u} AR)`.
- The local free presentation of M: `(hM : M.IsQuasicoherent)`, Mathlib's
  locally-cokernel-of-free-modules definition, with arbitrary generator and relation sets.
- A quasi-coherent O_U-module F: `(F : U.Modules) (hF : F.IsQuasicoherent)`.
  This is the general ringed-space quasi-coherence notion used in the recorded
  Coherent module, equivalent to affine-local tilde modules for schemes.
- The specified A-linear isomorphism u_* F ≅ M: `(e : (R).obj F ≅ M)`.
  `R` is exactly the pushforward functor used by the recorded affine correspondence:
  `SheafOfModules.pushforward` along `Opens.map f.base`, with target AR and
  ring map `𝟙 AR`. In particular, it retains the action of O_U(u⁻¹ W), rather than
  restricting to O_X(W). Its sections are F(u⁻¹ W).
- Conclusion, both directions: `M.IsFiniteType ↔ F.IsFiniteType`. On each of the two
  ringed spaces, this Mathlib predicate is a covering with finite generating families
  and epimorphic free maps. It includes the node's explicit sheaf-surjectivity clause.
- The parenthetical existence and uniqueness of F is background from the imported
  affine correspondence, not an extra conclusion or an assumption to restate.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf`: `SheafOfModules` and its category.
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`:
  `SheafOfModules.IsQuasicoherent` (via QuasicoherentData/Presentation).
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators`:
  `SheafOfModules.IsFiniteType` (via LocalGeneratorsData/GeneratingSections).
- `Sheaf.AlgebraicGeometry.Coherent`: its documented quasi-coherence and finite-type
  clauses use those same Mathlib predicates; its `RingedSpace.IsCoherent` is not needed.
- `Sheaf.AlgebraicGeometry.AffineModuleCorrespondence`:
  `AlgebraicGeometry.Scheme.Modules.affine_module_correspondence`; the module imports
  this dependency and uses precisely its direct-image algebra and module functor.
- `Sheaf.AlgebraicGeometry.TensorPullback`: `Scheme.Modules.tensorPullback` was read.
  The current statement only requires direct image; it uses the existing Mathlib
  pushforward as in the correspondence, not a second pullback or module definition.

The source files of Stacks were absent locally. Read the actual source online:
[0897](https://stacks.math.columbia.edu/tag/0897), proof, the finite-type passage;
[01SB](https://stacks.math.columbia.edu/tag/01SB), affine equivalence;
[01PB](https://stacks.math.columbia.edu/tag/01PB), affine finite-type criterion.
The general statement isolates the finite-type detail, so no Noetherian or proper
hypothesis from the surrounding cohomology theorem is required for this local lemma.

Edge cases checked before writing: empty U (M is isomorphic to the zero direct image),
empty X (then U is empty), zero F and M, identity morphisms, arbitrary non-surjective
and non-finite affine morphisms. Zero generators are allowed by IsFiniteType; no
nonemptiness, positive rank, Noetherian, characteristic, or finite morphism hypothesis
is imposed. All schemes, ring values and module values use universe u as in the
recorded correspondence; no independently smaller test universe occurs.

Searches performed (2026-10-11):

- msearch leanfinder: "An affine morphism preserves finite type for quasi-coherent
  modules over the direct image structure sheaf"; eight results about finite or
  finite-type scheme morphisms and sections, none the module statement.
- msearch loogle: "SheafOfModules.IsFiniteType"; four results giving the predicate,
  constructor, local generators and the finite-presentation instance, no affine theorem.
- msearch grep: "IsFiniteType.*pushforward|pushforward.*IsFiniteType"; zero hits.
- msearch leansearch: "finite type quasi-coherent modules under affine module
  correspondence"; service unavailable (Internal Server Error), no verdict inferred.
- rg over WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for the item id,
  `IsFiniteType.*pushforward|pushforward.*IsFiniteType|affine_module_finite_type`:
  no exact statement or name collision.
- rg for IsFiniteType/IsQuasicoherent in source AlgebraicGeometry/Modules:
  quasi-coherence and module descent declarations, no matching relative finite-type theorem.
- grep -rn for the item id in WeilConjectures: no hits.

The docstring carries all five proof steps of the DAG, including the affine image
formula, generation in both directions, and the finite-type affine criterion.
No disputed statement or node fault found. Server compilation passed cleanly in 3.3 s.

## Second reading by J1

Independently read the node, its five proof steps, the delivered Lean file, all seven
statement-dependency records, and their declarations. No mathematical or typing
mismatch found; the module and node record are retained verbatim. This delivery has
no new definition node, dependency module, or stage-2 statement correction.

Source check: the Stacks checkout is absent on this machine. Downloaded the actual
`coherent.tex`, `morphisms.tex`, and `properties.tex` into the item's scratchpad and
read the cited labels, including their statements and proofs; also checked the
[0897](https://stacks.math.columbia.edu/tag/0897),
[01SB](https://stacks.math.columbia.edu/tag/01SB), and
[01PB](https://stacks.math.columbia.edu/tag/01PB) pages. The line numbers match the
node's citations. In 0897 the surrounding cohomology result assumes Noetherianity,
a finitely generated graded algebra, and properness. The extracted finite-type
passage concerns the affine relative spectrum; its local argument uses only the
affine equivalence of 01SB and the affine finite-type criterion of 01PB, neither of
which assumes Noetherianity or properness. The subsequent identification of finite
type with coherence in 0897 does use Noetherianity and is not this node's conclusion.
Thus the generality of this node and its Lean statement is justified.

Item-by-item statement list and matching verdicts:

1. Objects: arbitrary schemes U and X and a morphism u:U -> X. Lean:
   `variable {U X : Scheme.{u}} (f : U ⟶ X)`. Read `Scheme` and `Scheme.Hom`, and
   `Scheme.Modules := SheafOfModules.{u} X.ringCatSheaf`. Verdict: exact objects;
   the variable name f instead of u changes nothing.
2. Hypothesis: u is affine, inverse images of all affine opens are affine. Lean:
   `[IsAffineHom f]`. Read the class field `isAffine_preimage` in Affine.lean:47.
   Verdict: exactly the recorded dependency, with no finite/proper assumption.
3. Object: the sheaf of rings A = u_* O_U on X, whose sections on W are
   O_U(u^-1 W). Lean notation `A` uses `TopCat.Sheaf.pushforward` on U.sheaf;
   `AR` applies `forget₂ CommRingCat RingCat` with `sheafCompose`. Verdict: exact
   direct-image ring sheaf; forgetting commutativity leaves rings and actions intact.
4. Object: a sheaf M of A-modules on X. Lean: `(M : SheafOfModules.{u} AR)`.
   Read SheafOfModules.lean:33 and its Hom structure: module-valued presheaf with
   sheaf underlying abelian groups and componentwise linear maps. Verdict: exact.
5. Hypothesis: M is locally the cokernel of a map between arbitrary free
   A-modules. Lean: `(hM : M.IsQuasicoherent)`. Read Presentation, QuasicoherentData
   and IsQuasicoherent in Quasicoherent.lean:43,202,251. Presentations consist of
   generators and generators of their kernel, with no finite-index requirement.
   Verdict: the node's exact local presentation, not finite presentation.
6. Object and hypothesis: F is a quasi-coherent O_U-module. Lean:
   `(F : U.Modules) (hF : F.IsQuasicoherent)`. Read Coherent.lean and its explanation
   of the recorded predicate: the ringed-space presentation notion is equivalent
   to the affine-local tilde notion on schemes. Verdict: the dependency's intended
   quasi-coherence, with no coherence or finite-type hypothesis imposed.
7. Hypothesis: an A-linear isomorphism u_* F ≅ M, where direct image retains the
   O_U(u^-1 W) action. Lean: `(e : (R).obj F ≅ M)`. Read both the recorded
   affine_module_correspondence signature and SheafOfModules.pushforward in
   PushforwardContinuous.lean:44, down to PresheafOfModules.pushforward:89.
   The same `Opens.map f.base` and identity ring map `𝟙 AR` are used here and in
   the dependency; sections and restriction maps come from F on inverse images,
   with restriction of scalars along the identity. Verdict: exact A-linear
   isomorphism. It does not use Scheme.Modules.pushforward with its O_X action.
8. Conclusion: M is finite type over A iff F is finite type over O_U. Lean:
   `M.IsFiniteType ↔ F.IsFiniteType`. Read GeneratingSections:44, its finite-index
   predicate:95, LocalGeneratorsData:113 and IsFiniteType:142 in Generators.lean.
   A covering and finite families with Epi of the free map express precisely local
   finite generation and sheaf-surjectivity. Verdict: both clauses and directions
   are exact; no assertion of sectionwise surjectivity on all opens is substituted.
9. Background parenthesis: F exists and is unique up to isomorphism by the affine
   correspondence. The imported theorem states the corresponding equivalence with
   the same direct-image functor. Verdict: background for the supplied F and e,
   not a further conclusion of this conditional finite-type lemma.

Dependency audit: the seven records use the Mathlib declarations and the landed
Coherent, TensorPullback and AffineModuleCorrespondence modules read above.
Tensor pullback is not used by this direct-image statement; its record was opened
and no private replacement introduced. The supplied correspondence's scalar
restriction and inverse constructions are background, not additional hypotheses
of affine_module_finite_type.

Edge cases: the empty schemes and empty inverse images are allowed; the empty
open cover covers the empty space. Zero modules and zero generators are allowed
(`Finite` does not mean `Nonempty`); arbitrary empty generator/relation families
are permitted in quasi-coherent presentations. No positive n, characteristic,
field, Noetherian, surjectivity, finite morphism, or nonempty-space condition appears.
All objects and sections live in the shared arbitrary universe u, as in the
recorded correspondence; choosing u large enough accommodates any given pair of
schemes and modules. Cover indices shrink to the site's universe via Mathlib's
shrink constructions; this imposes no size condition on a topological open cover.
There is no independent smaller test-object universe and no limit-index issue.

Independent searches (2026-10-11), with words other than the first reader's:

- msearch leanfinder: `locally finitely generated sheaf under relative spectrum
  equivalence`: eight hits, chiefly locallyOfFiniteType_iff and finite_app for
  morphisms, plus LocalGeneratorsData.IsFiniteType.isFiniteType; none this theorem.
- msearch loogle: `SheafOfModules.IsFiniteType, SheafOfModules.pushforward`:
  zero hits.
- msearch leansearch: `finite generation of sheaves of modules for relative Spec
  equivalence`: unavailable, Internal Server Error; no negative verdict inferred.
- rg for `IsFiniteType`, `finite_type`, `finiteType`, combinations with `affine`
  and `pushforward`, and the proposed declaration/item names across Mathlib's
  module-sheaf and scheme-module directories, all WeilConjectures sources,
  lean/Sheaf and dag/lean_names_upstream.json. Found the predicates, transport of
  generating sections by colimit-preserving functors, the affine generation lemma,
  and finite-type pullback statements; no relative affine finite-type equivalence
  or declaration-name collision. The generic transport statement is one direction
  under functor hypotheses, not this equivalence.

H5-H9 check: no new definitions and no hollow data; the single named theorem has
only `sorry`. Both docstrings name source tags and this blueprint id. Its five
numbered proof paragraphs follow the node's five steps, including the image-sheaf
argument in both directions, shrinking around f(y), and the affine criterion.
The single import supplies the dependency and all notions used. Namespace, header
and 100-character line bound conform. All scheme, morphism and universe variables
are explicitly bound; the recorded lean.statement is verbatim the file signature.

Validation: independently compiled the unchanged module with scompile.py on the
server: exit 0, 3.2 seconds, no warnings. Second reading changes only this report,
adding the independent source, dependency, clause, edge-case and search audit.
