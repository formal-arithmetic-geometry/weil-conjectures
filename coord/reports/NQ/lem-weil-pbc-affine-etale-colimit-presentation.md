## Worker report

The module `Sheaf.AlgebraicGeometry.AffineEtaleColimitPresentationFinite` states
`AlgebraicGeometry.Scheme.exists_affineEtale_colimit_presentation_finite` with a single
`sorry` proof. There are no definitions or additional theorems. The node is unchanged
except for its `lean` record. In particular, its existing statement correction is preserved.

Hypothesis correspondence:

- Nonempty directed preorder: `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. No antisymmetry is imposed.
- Inverse system of universe-u schemes: `D : Iᵒᵖ ⥤ Scheme.{u}`. All stages are qcqs
  by `CompactSpace (D.obj i)` and `QuasiSeparatedSpace (D.obj i)`; all transition
  arrows have `IsAffineHom (D.map a)`.
- Limiting cone: `c : Cone D`, `hc : IsLimit c`; its point is `c.pt`.
- The sites C_i and C are precisely `(D.obj (op i)).FullAffineEtale` and
  `c.pt.FullAffineEtale`. Their finite standard coverings and generated topologies
  are `fullAffineEtalePrecoverage` and `fullAffineEtaleTopology`.
- Transition functors and cone functors are `U` and `v`; the coherent comparisons
  are `gamma : U i j h ⋙ U j k h' ≅ U i k (h.trans h')` and
  `delta : U i j h ⋙ v j ≅ v i`.
- Normalization is `h0`, `h3`, `h4`, `h5`: identity transition functors, both
  degenerate gamma comparisons, and identity delta comparisons. `HEq` expresses
  identity comparisons across the functor equalities without introducing transports.
- Associativity of gamma is `h8`, evaluated at every object. Cone compatibility
  of delta with gamma is the objectwise equality `h9`.
- Cover preservation is `h10` for U and `h12` for v, using `Presieve.map`.
  All cospan pullbacks are preserved by `h11` and `h13` respectively.
- Continuity of both families is the first two existential binders of `h14`.
  Its remaining two conjuncts supply a left adjoint L for each continuous
  pushforward on `Type u` sheaves, as `Nonempty (L ⊣ ...sheafPushforwardContinuous...)`,
  with `PreservesFiniteLimits L`.
- Object descent is `h15`: every limit object is isomorphic to a stage image.
- Map descent is `h16`, including exactly the delta conjugation
  `f = delta.inv.app A ≫ (v j).map g ≫ delta.hom.app B`.
- Eventual equality of maps whose v-images agree is `h17`, with a later j and
  equality of their U-images.
- Descent and reflection of finite covering families is `h18`, an iff for
  `Fin n`, including target isomorphism t, source isomorphisms s and the commuting
  equations `(v i).map (fi a) ≫ t.hom = (s a).hom ≫ f a`.

Conclusion correspondence, in displayed order:

- The existential `F : I ⥤ Cat.{u, u + 1}` is a strict diagram. Q supplies its
  precoverages; e and v' are the requested functors, with `theta` and `eta` having
  exactly the two natural-isomorphism signatures in the node.
- `∀ i, (e i).IsEquivalence` makes each e an equivalence. The following existential
  class binders give Q isomorphism coverings, finite indexed composition, finite
  indexed base change and covering pullbacks. Finiteness of every covering
  presieve is `R ∈ Q i A → Finite R.uncurry`.
- The next iff states that e preserves and reflects standard covers.
- Transition cover preservation is the following implication using
  `R.map (F.map (homOfLE h)).toFunctor`; the next conjunct is preservation of every
  `cospan f g` limit by this same transition functor.
- Strict cone compatibility is `(F.map (homOfLE h)).toFunctor ⋙ v' j = v' i`.
  The following `Arrow.mk ... = Arrow.mk ...` is precisely the theta/eta/delta
  composite equality, including source and target objects despite strict functor
  equalities not being definitional equalities.
- The next existential binders and two conjuncts give continuity and
  finite-limit-preserving left adjoints to the continuous pushforwards for
  both transitions and v', again with coefficient category `Type u`.
- `K : Cocone F`, `W : K.pt ⥤ c.pt.FullAffineEtale`, and `P : Precoverage K.pt`
  are existentially quantified. The two `Nonempty (IsColimit (...mapCocone K))`
  clauses use `Cat.objects` and `Cat.arrows`, so both are actual set colimits.
- `(K.ι.app i).toFunctor ⋙ W = v' i` is strict equality.
- The next iff defines membership in P exactly as a stage covering Ri mapped
  by K_i, transported by `h ▸ ...` along equality of its target with A.
- P has `HasIsos`, `IsStableUnderFiniteComposition`, `IsStableUnderFiniteBaseChange`
  and `HasPullbacks`. The final two clauses say `W.IsEquivalence` and
  `R ∈ P A ↔ R.map W ∈ fullAffineEtalePrecoverage c.pt (W.obj A)`.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and its category.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `AlgebraicGeometry.IsAffineHom`.
- `def-weil-pbc-scheme-conventions` deliberately has no declaration: the qcqs
  clauses use the recorded Mathlib `CompactSpace` and `QuasiSeparatedSpace` notions.
- `Sheaf.AlgebraicGeometry.FullAffineEtaleSite`:
  `AlgebraicGeometry.Scheme.FullAffineEtale`, `fullAffineEtalePrecoverage`,
  `fullAffineEtaleTopology`; their full definitions and accompanying docstrings
  were read, including the empty covering and universe conventions.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: the recorded
  `CategoryTheory.Limits.pullback` definition and projection signatures were read.
  This statement uses its universal-property form `PreservesLimit (cospan f g)`.
- `Mathlib.CategoryTheory.Sites.Continuous` (through `Sites.Pullback`):
  `CategoryTheory.Functor.IsContinuous`, `sheafPushforwardContinuous`; sites and
  sheaves are the recorded Mathlib `Precoverage`, `Sheaf`, `toGrothendieck`.
- `Mathlib.CategoryTheory.Limits.HasLimits`: `Cocone`, `IsColimit` (underlying
  structures read in Cones/IsLimit), for the category-colimit dependency.
- `Sheaf.CategoryTheory.FinitePrecoverage`: the exact recorded
  `CategoryTheory.Precoverage.IsStableUnderFiniteComposition` and
  `IsStableUnderFiniteBaseChange` classes, with their finite-index quantifiers.
- `Sheaf.CategoryTheory.ArrowsFunctor`: the existing `CategoryTheory.Cat.arrows`
  functor, whose object and map definitions were read. `Cat.objects` is Mathlib's
  existing object functor, also read in full.
- Proof dependency `Sheaf.AlgebraicGeometry.AffineEtaleDescentData` is imported
  non-publicly as required by the proof-plan convention; its declaration
  `AlgebraicGeometry.Scheme.affineEtale_descent_data` was read.

Source checks: read the local Stacks text at Categories 004A, Sites 0A34/09YL,
and Étale Cohomology 0EYL. Sites explicitly restricts to finite index sets and
identifies both objects and arrows with filtered set colimits. The theorem
preserves the current node's normalized-system formulation and all its clauses.

Edge cases checked: n = 0 remains available in h18 and in the imported standard
precoverage; the empty scheme and its empty covering are allowed. No positive
cardinality or nonempty-object assumption was added. Singleton index preorders,
non-antisymmetric preorders, identity transitions and degenerate coherent
comparisons are retained. The index universe equals the scheme universe u;
site objects and strict diagram objects live in u+1 with hom universe u.
Coefficients stay Type u. Finite composition/base change do not impose the
withdrawn unrestricted indexed axioms. No geometric p/q natural transformations
are assumed: those belonged to the obsolete attachment, not this node.

Searches for existing declarations:

- `msearch.py ... leansearch "strictification of directed system of sites with finite
  coverings and category colimit"`: service unavailable, Internal Server Error;
  this is not evidence of absence.
- `msearch.py ... leanfinder "strictify coherent directed system of affine etale sites
  with finite covers and identify its category colimit"`: eight hits, including
  `AffineZariskiSite.isColimitCocone`, `nonempty_isColimit_Γ_mapCocone`, and affine
  scheme colimits; none states this site strictification/comparison theorem.
- `msearch.py ... loogle "CategoryTheory.Cat, CategoryTheory.IsFiltered"`: one hit,
  `instIsFilteredGrothendieckOfαCategoryObjCat`, concerning filtered Grothendieck
  constructions, not this theorem.
- `msearch.py ... grep "affineEtale.*colimit|affine_etale.*colimit|strictification"`:
  zero Mathlib hits. `rg` of upstream WeilConjectures for strictification and
  colimit_presentation, and for this blueprint id, found no match.
- `rg` of project `lean/Sheaf` found the obsolete module
  `AffineEtaleColimitPresentation.lean`: its theorem adds p and q data, requires
  unrestricted indexed covering axioms, and proves the existential by false
  elimination from a withdrawn strictification interface. It does not state the
  current node. No existing record is used for that different assertion. The new
  finite theorem has a distinct name and module; no notion is defined twice.
- The new full theorem name was searched in project Lean and upstream name
  records: no match.

Validation: every delivered Lean file was compiled with scompile.py on the server,
nice 19, two threads, 60 seconds per file; initial compile clean (1.8 seconds).
The delivery dry run is the final check. The independent second reader supplies
its own reading after this worker finishes.

## Second reading by NQ

Independent second reader, 2026-10-15. I read the sandbox node and module,
the current repository node, all eight statement-dependency records, their
relevant declarations, and the proof-dependency module AffineEtaleDescentData.
There are no new nodes or dependency modules in this delivery.

Source first: Categories 004A constructs split replacements using labelled pairs;
Sites 0A34 explicitly assumes finite covering index sets, and 09YL constructs the
category by colimits of both object and arrow sets and takes images of stage
coverings. Etale Cohomology 0EYL first treats qcqs stages, descends affine etale
objects and maps, and makes finite descended coverings surjective at a later
stage. The node isolates the categorical assembly, taking the coherence and
descent assertions as hypotheses; it does not assert that arbitrary functors are
geometric base change. The Lean correctly follows this isolation, without adding
p/q pullback squares or a Noetherian, separated, characteristic, or field condition.

The finite-index correction is inherited verbatim from the base, not made by
this worker. Its replacement of unrestricted indexed composition/base change
by finite indexed axioms agrees with 0A34 and 09YL. I searched all direct
stmt_deps/proof_deps citers: there is exactly one,
lem-weil-pbc-affine-etale-site-colimit. I read its statement and all four proof
steps: its application still supplies coherence, both morphism descent assertions,
and finite covering descent, so the recorded holds:true remains valid. A second
direct citer does not exist. I also read the downstream
lem-weil-pbc-etale-cohomology-limit-of-schemes: it uses the same qcqs finite-site
limit comparison, so the correction does not alter its asserted cohomology
isomorphism. No new statement correction is needed.

Node inventory and exact Lean correspondence (each row passes):

| Object or hypothesis in the node | Lean rendering and verdict |
| --- | --- |
| Nonempty directed preorder | I : Type u, Preorder I, Nonempty I, IsDirected I (le); no antisymmetry. Exact. |
| Inverse schemes, affine arrows, qcqs stages | D : I.op functor to Scheme.{u}; CompactSpace and QuasiSeparatedSpace for every D.obj i; IsAffineHom for every D.map a. Exact. |
| Limit X and its cone | c : Cone D, hc : IsLimit c, X = c.pt. Exact. |
| Full affine etale categories and finite covers | (D.obj (op i)).FullAffineEtale and c.pt.FullAffineEtale, with fullAffineEtalePrecoverage and fullAffineEtaleTopology. Exact recorded definitions. |
| Coherent functors and comparisons | U, v, gamma : U_ij followed by U_jk iso U_ik, delta : U_ij followed by v_j iso v_i. Exact directions. |
| Normalization | h0 is U_ii = identity; h3 and h4 are the two degenerate gamma identities; h5 is delta_ii identity. HEq avoids arbitrary transport choices. Exact. |
| Associativity and cone cocycles | h8 is gamma associativity at every A; h9 is v_k(gamma.hom) followed by delta_ik = delta_jk followed by delta_ij. Exact. |
| Covers and every cospan pullback preserved | h10/h12 use Presieve.map on all covering presieves; h11/h13 use PreservesLimit (cospan f g) on every cospan. Exact. |
| Continuity and left exact left adjoints | h14 existentially binds IsContinuous for both families, then each left adjoint L to sheafPushforwardContinuous with PreservesFiniteLimits L. Coefficients are Type u. Exact. |
| Object descent | h15 quantifies every limit-site A, then a stage i and Ai with Nonempty (v_i Ai iso A). Exact. |
| Map descent | h16 quantifies i,A,B,f before j,h,g and requires f = delta.inv.app A followed by v_j.map g followed by delta.hom.app B. Exact conjugation and order. |
| Eventual equality | h17 assumes v_i.map f = v_i.map g, then finds j >= i with equal U_ij images. Exact. |
| Descent and reflection of finite covers | h18 quantifies n,A,B,f before the iff and stage witnesses; t and s are target/source isomorphisms, with v_i(fi_a) followed by t.hom = s_a.hom followed by f_a. Exact. |

Conclusion inventory, in the node's order (each row passes):

| Conclusion clause | Lean rendering and verdict |
| --- | --- |
| Strict diagram and comparison data | Existential F : I functor to Cat.{u,u+1}, Q, e, v', theta and eta, with exactly the node's functor directions. Exact. |
| Equivalences and four finite site properties | Every e_i.IsEquivalence; existential HasIsos, IsStableUnderFiniteComposition, IsStableUnderFiniteBaseChange and HasPullbacks for Q_i. Exact. |
| Every stage covering presieve is finite | R in Q_i A implies Finite R.uncurry, for every A,R. Exact, not merely a finite refinement. |
| e preserves and reflects coverings | R in the original precoverage iff R.map (e i) in Q_i. Exact. |
| Strict transitions preserve covers and pullbacks | The next implication uses map of F.map (homOfLE h); the next conjunct is PreservesLimit for every cospan. Exact. |
| Strict compatibility of v' | F_ij followed by v'_j = v'_i as functors. Exact equality, not just an isomorphism. |
| theta/eta/delta compatibility | Equality of Arrow.mk of v'_j(theta.hom_A), eta_j.hom_(U_ij A), delta_ij.hom_A with Arrow.mk (eta_i.hom_A). Exact, including endpoints. |
| Continuous transitions and v', with left adjoints | The following existential IsContinuous binders and L/adjunction/PreservesFiniteLimits clauses use Q_i.toGrothendieck and Type u. Exact for both families. |
| Colimit data | Existential K : Cocone F, W : K.pt functor to the limit site, and P : Precoverage K.pt. Exact. |
| Actual object and arrow set colimits | Nonempty (IsColimit (Cat.objects.mapCocone K)) and the corresponding Cat.arrows clause. Exact universal properties, not just joint surjectivity. |
| Strict induced comparison | Every K_i followed by W = v'_i. Exact. |
| P is exactly the union of stage cover images | For all A,R, membership iff there are i,Ai,Ri and h : K_i(Ai)=A with Ri covering and h-transport of Ri.map K_i equal to R. Exact, with equality of targets rather than extra isomorphism closure. |
| Colimit finite site axioms | P.HasIsos, P.IsStableUnderFiniteComposition, P.IsStableUnderFiniteBaseChange, P.HasPullbacks. Exact. |
| Equivalence and detection of covers | W.IsEquivalence and, for every A,R, R in P iff R.map W is a standard covering. Exact. |

Dependency checks: FullAffineEtale is the full subcategory of S.Etale on
IsAffine domains, not the spectrum-only category S.AffineEtale. Its precoverage
uses an actual Fin n family, etale arrows and joint surjectivity. Its topology
is generated from that precoverage. FinitePrecoverage quantifies over finite
index types, allowing repetitions and empty families. Mathlib HasIsos and
HasPullbacks have the stated singleton-isomorphism and covering-pullback
meanings. Mathlib IsContinuous is sheaf preservation by precomposition; the
separate cover and cospan clauses retain the Stacks continuity requirements.
The adjunction has the correct direction: sheaves on the source site to sheaves
on the target site, left adjoint to precomposition. Cat.objects reads the actual
object type; Cat.arrows sends each Arrow to its functor image including both
endpoints. Cocone and IsColimit have their usual factorization and uniqueness
fields; pullback is limit of cospan. Scheme and IsAffineHom are the recorded
Mathlib notions. The conventions node intentionally defines nothing new.
AffineEtaleDescentData is a proof-only import; its geometric p/q assumptions
are not silently introduced as hypotheses here.

Edge cases: I cannot be empty because the node expressly says nonempty;
singleton and non-antisymmetric directed preorders are allowed. Fin 0 is
available in h18, and empty-domain schemes and empty covering families remain
allowed by the imported precoverage. No stage or site object is required to
be inhabited. There is no ring characteristic or positive dimension parameter.
The single universe u binds I and Scheme, with Cat hom universe u and object
universe u+1, and Type u coefficients as required by the project convention.
All variables and universes are explicitly bound; no independent smaller
universe makes a test condition vacuous.

Independent searches, using different phrases from the first reader:

- LeanFinder: "equivalence between filtered colimit category and affine etale
  site finite coverings" returned eight hits, principally the small etale
  topologies, AffineZariskiSite.isColimitCocone, and affine-transition geometric
  limit results. None is this assembly theorem.
- Loogle: "CategoryTheory.Functor.IsEquivalence,
  CategoryTheory.Limits.IsColimit" returned no hits.
- LeanSearch: "A coherent directed system of categories with finite covering
  families has a strict colimit presentation equivalent to its descent
  category" was unavailable (Internal Server Error). No absence inference.
- msearch grep for "FullAffineEtale|colimit_presentation_finite|strictification"
  returned no Mathlib match. Independent rg over upstream WeilConjectures,
  Mathlib CategoryTheory/Sites, and project AlgebraicGeometry/CategoryTheory
  found the colimit-site helpers and the obsolete unrestricted presentation.
  I opened that presentation's conclusion and proof: it demands unrestricted
  composition/base change and ends by the withdrawn contradiction route; it is
  not an existing declaration of the corrected node. The new theorem introduces
  no duplicated definition. The named theorem is absent from upstream.

No signature mismatch, missing dependency, hollow definition, extra theorem,
proved statement, unbound variable, forbidden local notation or overlong Lean
line was found. The module and theorem docstrings name the source and blueprint;
the theorem docstring gives the labelled-pair strictification, transport of site
properties, object/arrow colimits, equivalence argument, and covering comparison.
I left the valid Lean and node record unchanged and appended only this review.

Validation: the complete delivered module passed scompile.py on the server in
1.9 seconds, nice 19, two threads, 60-second per-file limit, with no diagnostic.
The raw file signature is verbatim equal to lean.statement. The delivery dry
run passed compilation and preflight (OK); no Lean or node edits were necessary.
