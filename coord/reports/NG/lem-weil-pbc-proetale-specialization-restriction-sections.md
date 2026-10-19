## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleSpecializationRestrictionSections` states
`AlgebraicGeometry.Scheme.isIso_proEtaleUnit_sections_of_specialization` with proof `sorry`.
It introduces no definition and changes only the item's `lean` record.

Source read: `literature/stacks-project/proetale.tex`, Tag 09AC,
`lemma-compute-i-star`, statement and proof (lines 4987–5025), together with the
item's seven-step DAG proof. The module docstring carries that proof plan,
including its correction from specialization-stability to generalization-stability
for images of flat maps. The mathematical statement is unchanged.

Each hypothesis and clause is rendered as follows:

- Schemes and closed immersion: `{X Z : Scheme.{u}} (i : Z ⟶ X)
  [IsClosedImmersion i]`.
- Object of the small pro-etale site: `(V : X.ProEt)`. Its structure morphism
  `V.hom` is weakly etale by the site's defining property; it is not an arbitrary
  scheme over `X`.
- Affineness: `[IsAffine V.left]`.
- Weak contractibility, exactly as defined inline in the node: `hweak` quantifies
  over every `P Q : Sheaf (ProEt.topology X) (Type (u + 1))` and every morphism
  `φ : P ⟶ Q`, and requires `Epi φ → Function.Surjective (φ.hom.app (op V))`.
  There is no additional geometric contractibility or covering hypothesis.
- Every point specializes into the closed fibre: `hspec` says that for every
  `x : V.left` there is `z : ↥(pullback V.hom i)` such that
  `Specializes x ((pullback.fst V.hom i) z)`. Mathlib's `Specializes x y` means
  `y ∈ closure {x}`, so the direction agrees with the source.
- The actual map is the recorded `proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}`
  unit, whiskered with `(sheafSections (ProEt.topology X)
  AddCommGrpCat.{u + 1}).obj (op V)`. Its component at any abelian sheaf `F` is
  exactly `((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app F).hom.app
  (op V)`, an abelian-group homomorphism.
- The source group is `F.obj.obj (op V)`. The target is the inverse-image sheaf
  evaluated on `(proEtaleBaseChange i).obj V`: the base-change declaration uses
  `pullback V.hom i` and its second projection to `Z`, so this is precisely
  `(i⁻¹ F)(V ×[X] Z)` with the same chosen fibre product used in `hspec`.
- The conclusion `IsIso` of this natural transformation asserts every component
  is an isomorphism. Naturality in `F` is part of its type: this is a natural
  transformation obtained from the existing unit by `Functor.whiskerRight`.
  Thus naturality is retained without selecting an unrelated family of isomorphisms.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`
  (lines 35–77, signatures and docstrings).
- `Mathlib.AlgebraicGeometry.Sites.Proetale`: `Scheme.ProEt`, its weakly-etale
  object instance, `Scheme.ProEt.precoverage`, and `Scheme.ProEt.topology`
  (lines 92–157). The mathlib-status dependency needs no replacement `lean` record.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`: `Scheme.proEtaleBaseChange`,
  `proEtaleSheafInverseImage`, `proEtaleSheafDirectImage`, and
  `proEtaleSheafAdjunction` (full declaration signatures and docstrings read).
  Also read the actual sectionwise `ProEtale.lowerStar` in the supplied
  `FiniteCoefficient/UpperLowerStar/Defs.lean` framework and
  `MorphismProperty.Over.pullback` in Mathlib `OverAdjunction.lean` to verify
  the target and the order of the chosen product.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`:
  `AlgebraicGeometry.IsClosedImmersion` (lines 40–46).
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`:
  `CategoryTheory.Limits.pullback`, `pullback.fst`, and `pullback.snd`
  (lines 85–118). These are available through the statement dependency imports.
- `Mathlib.CategoryTheory.Sites.Sheaf` (available through the recorded module
  `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`): `Sheaf` and `sheafSections`
  (lines 301–338). Only the abelian-sheaf/evaluation part of the sites/cohomology
  node is used; no cohomology comparison is needed.

The module imports all currently recorded proof-dependency modules, non-publicly
unless they are already statement imports. The genuinely unstated proof lemma
`lem-weil-pbc-affine-closed-inverse-image-evaluation` has no module to import yet;
its future proof import can be added when it lands. It is not needed to type
this statement and is not a prerequisite wait.

Edge cases checked: if `V` is empty, `hspec` is vacuous and the source and target
section groups are zero, so the unit is an isomorphism. If `Z` is empty, `hspec`
forces `V` empty; no false nonempty-fibre assumption was added. If `i` is the
identity, specialization is reflexive after the canonical fibre identification
and the unit is an isomorphism. The zero abelian sheaf is allowed. No reduced,
Noetherian, quasi-compact-base, or coefficient-ring hypothesis was added.
Universes are explicit: schemes have universe `u`, site objects `u+1`, site Homs
`u`, and sets/abelian groups `u+1`, following the dependency and size convention.

Searches actually run with `msearch.py NG` and this item's id:

- LeanFinder: "Sections of a pro etale abelian sheaf on a weakly contractible affine
  agree with inverse image along a closed immersion when all points specialize into
  the closed fiber" returned eight hits: affine-transition-limit structure-sheaf
  section equalities/vanishing, germ-injective lifting, and `toΓSpecCApp_iff`.
  Their returned signatures concern structure sheaves and limits, not arbitrary
  abelian pro-etale sheaves or the closed-immersion unit; no match.
- Loogle: `CategoryTheory.Sheaf, IsIso` returned no hits with the diagnostic
  "unknown identifier 'IsIso'"; this query is inconclusive, not an absence claim.
- Grep: `specialization|WeaklyContractible|weaklyContractible` in Mathlib
  `AlgebraicGeometry/Sites` returned no hits.
- LeanSearch: "Pro etale sheaf sections closed immersion weakly contractible
  specialization" was unavailable (Internal Server Error), recorded as unavailable.
- Local `rg` in the upstream source and project `lean/Sheaf`, by the item id and
  `specialization.*[Ss]ection|[Ss]ection.*specialization`, found unrelated
  topological spectral restrictions and etale stalk specialization results.
- Local `rg` by `isIso_proEtaleUnit_sections_of_specialization|compute_i_star|
  computeIStar|specializationRestriction` found only a private structure-module
  helper in `EtaleAffineSingletonTensorDegreeHom.lean`, not this statement.
- Inspected existing weak-contractibility uses in `lean/Sheaf` and DAG: they concern
  covers or point left Kan extension, not this closed-fibre unit theorem.

No statement dispute, new node, dependency repair, or statement correction is needed.

Validation: the delivered module compiled cleanly via the required `scompile.py`
wrapper (no errors and no warnings). The first attempt exposed a coercion ambiguity
in a point binder and an unqualified `whiskerRight`; both were repaired by an
explicit scheme-carrier coercion and `Functor.whiskerRight`. No hypothesis changed.

## Second reading by NG

I independently read the node, the delivered Lean file, Stacks `proetale.tex`
Tag 09AC (`lemma-compute-i-star`, including its proof), and the signatures and
implementations of the statement dependencies. The following is my object,
hypothesis and conclusion checklist, with the Lean rendering and verdict.

- Two arbitrary schemes and their closed immersion: `{X Z : Scheme.{u}}`
  and `(i : Z ⟶ X) [IsClosedImmersion i]`. Correct. Mathlib's scheme structure
  and scheme Hom are the recorded objects; its closed-immersion class requires
  a closed embedding and surjectivity on stalks, the equivalent recorded notion.
- A genuine small-site object `V → X`: `(V : X.ProEt)`. Correct. I read
  `Scheme.ProEt` and `ProEt.topology` in Mathlib: this is the full category of
  weakly etale schemes over `X`, with the pro-etale covering topology. In
  particular `V.hom` is weakly etale, with no extra assumption needed.
- Affineness of that object: `[IsAffine V.left]`. Correct; no condition on
  affineness of `X` or `Z` is imposed.
- Weak contractibility: `hweak` quantifies over all set sheaves `P Q` on this
  same site and every morphism `φ`, and says `Epi φ → Function.Surjective
  (φ.hom.app (op V))`. Correct, exactly the node's explicit definition. This
  is neither an arbitrary ring-splitting assumption nor contractibility on a
  different basis site.
- The closed fibre: `pullback V.hom i`. Correct. I read the recorded
  fibre-product construction and its two projections. The first projection
  lands in `V.left`, the second in `Z`.
- The specialization hypothesis: `hspec : ∀ x : V.left, ∃ z :
  ↥(pullback V.hom i), Specializes x ((pullback.fst V.hom i) z)`.
  Correct. Mathlib's `specializes_iff_mem_closure` in `Topology/Inseparable`
  says exactly that the second point lies in the closure of the first.
  Thus each point of `V` specializes into the closed fibre, in the source's
  direction; it does not require every fibre point to specialize back.
- Every abelian sheaf `F` and the prescribed map: the conclusion is `IsIso`
  of the adjunction unit whiskered by the sections functor at `V`, for
  `AddCommGrpCat.{u + 1}`. Correct. At `F` the component is
  `((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app F).hom.app
  (op V)`. I read `proEtaleBaseChange`, `proEtaleSheafInverseImage`,
  `proEtaleSheafDirectImage` and `proEtaleSheafAdjunction` in the dependency
  module. They use actual base change, Kan extension, sheafification and its
  adjunction. I also read `ProEtale.lowerStar` in the exact supplied framework
  `lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/UpperLowerStar/Defs.lean`
  and `coord/pefw-upstream-framework.md`: direct image evaluates by this same
  base change. Consequently the source is `F(V)` and the target is precisely
  `(i⁻¹F)(V ×[X] Z)`, using the same chosen fibre product as `hspec`.
- Isomorphism and naturality: `IsIso (Functor.whiskerRight ...unit ...sections)`
  is equivalent to all those component maps being isomorphisms. Correct;
  naturality is built into the transformation, with no chosen unrelated family
  of isomorphisms. The sheaf is universally quantified by the transformation's
  domain, after the hypotheses on `i` and `V`, as required.

Source context: Tag 09AC imposes just a closed immersion, an affine weakly
contractible site object and the stated specialization condition. No global
Noetherian, characteristic, separatedness or coefficient finiteness assumption
was suppressed. The Lean does not add one. Its docstring follows all seven DAG
proof steps (localization; affine-site counit and flat going-down; splitting and
uniqueness; splitting finite covers; weak contractibility on the closed fibre;
canonical inverse-image evaluation; transport and naturality). The use of
**generalization** stability for flat images is correct, correcting the word
“specialization” in the source proof, without changing its statement.

Edge cases: the empty `V` satisfies `hspec` vacuously and both section groups
are terminal/zero by the empty covering. Empty `Z` forces `V` empty by `hspec`.
The identity immersion is included, with reflexive specialization after the
fibre-product identification. Zero abelian sheaves are included. There is no
integer/degree, index-set, characteristic or nonzero-ring restriction. Arbitrary
scheme universe `u` is bound explicitly; site objects have universe `u+1`, Homs
`u`, and sets and abelian groups `u+1`, consistent with the recorded convention.
No equality of the site object and Hom universes is imposed.

Independent searches (different wording from the first reader):

- LeanFinder via `msearch.py`: “A weakly contractible object of the proetale
  site has the same abelian sheaf sections as its closed fibre when every point
  specializes into that fibre”. Eight hits concern skyscraper stalks,
  condensed underlying sections or site-point fibre functors. Their returned
  signatures do not state this result.
- Loogle via `msearch.py`: `"Sheaf", "unit"` succeeds with twelve hits, all
  auxiliary unit/Yoneda constructions in `CategoryTheory.Comma.Presheaf.Basic`;
  none concerns this closed-immersion restriction statement.
- LeanSearch via `msearch.py`: “Closed immersion inverse image unit is an
  isomorphism on sections at a weakly contractible affine object”. Service
  unavailable (Internal Server Error); no absence inference from this service.
- `rg` on upstream `WeilConjectures`, project `lean/Sheaf`, Mathlib site sources
  and the exact supplied pro-etale framework, using specialization/unit/section,
  closed-fibre/section and compute-i-star variants. No exact existing theorem.
  Read the nearby project `shriek_sections_subsingleton_of_specializes_closed`:
  it concerns shriek vanishing, has no contractibility assumption and is not
  the unit isomorphism here. Ring w-contractibility and weakly-contractible
  evaluation/cover lemmas also have different conclusions.

No mismatch was found, so I left the module and node unchanged. There are no
new nodes or dependency modules to audit, no private definitions or hollow data,
and the only proof is the named theorem's `sorry`. The blueprint/source
references, 100-character lines and explicit binders were checked. A direct
text comparison confirms `lean.statement` is verbatim the theorem signature.

Independent validation: the sole delivered file compiled cleanly through
`scompile.py` on the server (sandbox 1.9 s, library 2.2 s), with no diagnostics.
An initial invocation used a relative path from the read-only checkout and
failed to find the sandbox file; the absolute sandbox path fixed the invocation.
