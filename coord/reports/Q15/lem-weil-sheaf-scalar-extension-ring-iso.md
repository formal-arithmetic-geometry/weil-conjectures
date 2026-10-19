## Worker report

The module `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso` states
`SheafOfModules.exists_scalarExtensionRingIso`, with `sorry` as its sole theorem proof.
The helper `scalarExtensionRingIsoTmul` is a real construction: evaluation of the existing
module-sheafification adjunction unit on the existing scalar-extension tensor presheaf.
It introduces no independently chosen map, tensor, or module category. No node correction,
new node, or dependency repair was needed. The previous run's superseded dispatch concerned
Q17's stage-1 split, not a stage-2 declaration; the current split was read in full.

The source was read in `literature/stacks-project/sites-modules.tex`: the change-of-rings
construction immediately preceding `lemma-adjointness-tensor-restrict` (03CZ), the module
sheafification discussion at 03CY, and `section-tensor-product` (03EK). The three tags
were checked in `tags/tags`. Stacks itself writes the scalar factor first. The recorded
change-of-rings dependency uses this convention too: Lean's `s ⊗ x` represents the node's
`x ⊗ s` under the ordinary tensor symmetry, with the target scalar acting on that factor.
The explicit formula therefore retains exactly the node's normalization.

Hypotheses and clauses, matched individually:

- The small site is `{C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}`.
  The site and morphism universes remain independent. A covering-family site gives this
  topology through the dependency's `Precoverage.toGrothendieck`; nothing in this theorem
  requires a particular presentation of the topology or extra coverings.
- `R S : Sheaf J CommRingCat.{r}` are the two commutative ring sheaves and `c : R ≅ S`
  is their given isomorphism. No stalk, point, flatness or scheme hypothesis appears.
- Every `M` is quantified in the dependency's transparent `ringedSiteModules` category.
  Modules are in the common value universe `max r m`, so scalar-extension tensors and
  the original abelian sheaf have the same universe. This is the ordinary common
  ambient-universe convention; neither ring and site nor object and morphism universes
  are identified. The sheaf-composition and abelian sheafification typeclasses expose
  the standard constructions used by the recorded tensor dependency. They hold for
  small sites in an adequate universe and impose no geometric or coefficient property.
- `M^(c)` is exactly `(SheafOfModules.restrictScalars
  ((sheafCompose J (forget₂ CommRingCat RingCat)).map c.inv)).obj M`.
  I read `SheafOfModules.restrictScalars` and `PresheafOfModules.restrictScalarsObj`:
  the latter uses `ModuleCat.restrictScalars` at every object, retaining all additive
  groups and restriction functions; the former retains `M.isSheaf` itself. The action
  is therefore `s • x = c.inv(s) • x`, not the forward action.
- The asserted functor already exists as this `restrictScalars`: on morphisms it uses
  `PresheafOfModules.restrictScalars.map`, itself the unchanged sectionwise linear map
  under `ModuleCat.restrictScalars`. Identities and composition are its functor laws.
- The existential `theta : ∀ M, changeOfRingsOfUniverses c.hom M ≅ ...` gives one family
  of actual S-module-sheaf isomorphisms, rather than a bare nonempty choice per object.
  `changeOfRingsOfUniverses` is the recorded dependency's sheafification of the
  sectionwise extension tensor. Its target-ring action is on the scalar factor.
- `scalarExtensionRingIsoTmul c.hom M U x s` is exactly the unit image of the pure tensor
  `s ⊗ x`, via `PresheafOfModules.sheafificationAdjunction (𝟙 _)`. This unit forgets to
  `CategoryTheory.toSheafify`, as witnessed by the existing Mathlib theorem
  `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`. It does not use
  any surjectivity assumption on the section map.
- The first conjunct is the forward formula at every object and every pair of sections:
  `(theta M).hom.val.app U (...) = (c.inv.hom.app U) s • x`.
- The second conjunct gives the inverse at every section of the original sheaf:
  `(theta M).inv.val.app U x = scalarExtensionRingIsoTmul c.hom M U x 1`.
- The last conjunct quantifies over all `M N` and `h : M ⟶ N` and is precisely the
  naturality square between `changeOfRingsHomOfUniverses` and `restrictScalars.map h`.
  Thus the same family satisfying both section formulas is natural in M.

Dependency declarations and their modules were opened and read:

- `CategoryTheory.Precoverage.IsSiteForCoverings` in
  `Sheaf.CategoryTheory.SiteCoveringAxioms`; its inherited `Precoverage.toGrothendieck`
  and `Sheaf` supply the general site convention.
- `CategoryTheory.ringedSiteModules` in `Sheaf.CategoryTheory.RingedSiteModules`:
  transparent abbreviation of Mathlib's `SheafOfModules`, used in every module binder.
- `SheafOfModules.siteSheafTensorRightMap` in the recorded
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, with its public
  import `TensorProductOfUniverses`: the latter's `changeOfRingsPresheafOfUniverses`,
  `changeOfRingsOfUniverses`, `changeOfRingsHomOfUniverses`, and identity-local-bijection
  lemmas are the actual scalar-extension construction used here.
- `CategoryTheory.presheafToSheaf`, `toSheafify`, and `sheafificationAdjunction` in
  `Mathlib.CategoryTheory.Sites.Sheafification`, publicly inherited from the tensor
  imports; no second sheafification is defined.
- Proof dependency `def-weil-presheaf-modules-sheafification` records
  `PresheafOfModules.sheafification` and its adjunction in
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (also explicitly imported
  for the proof plan). Its universal property is used in the docstring's steps 5 and 6.
- Proof dependency `def-weil-pbc-module-tensor-product` is a Mathlib leaf, not an absent
  Lean record: its exact match is `TensorProduct`, `TensorProduct.lift`, generation,
  and `LinearMap.rTensor`, inherited through the tensor imports.

The theorem docstring follows all six steps of the current Q17 split: inverse scalar
transport; the balanced map; restriction compatibility; the presheaf inverse; descent
and both inverse identities by module-sheafification uniqueness; naturality by that
same uniqueness. All universes and variables are explicitly bound. Definitions have
real data; the only postponed theorem matches the assigned DAG node.

Edge cases checked: zero module; zero ring (an isomorphism forces both rings zero);
identity c; a nontrivial ring automorphism (swap on A × A, confirming the inverse
rather than forward scalar action); empty site; empty covering families. No argument
uses enough points, surjectivity of the sheafification unit on sections, or global
pure-tensor representatives. All cases preserve the section formulas. There is no
STATEMENT-DISPUTED flag or detected node fault.

Searches actually run during this worker session (msearch logs record them):

- LeanFinder: "Extension of scalars along an isomorphism of sheaves of rings is naturally
  isomorphic to restriction along its inverse with normalized pure tensors". Eight hits:
  free-module pullback comparisons and `pushforwardCongr`/`pushforwardNatIso`; none
  states the normalized scalar-extension comparison for arbitrary module sheaves.
- Loogle: `SheafOfModules.restrictScalars`. Four hits: the existing functor, additivity,
  and its object/map formulas. Reused it for the transported module functor.
- msearch grep: `changeOfRings.*[Ii]so|scalarExtension.*[Ii]so|restrictScalars` in
  `Algebra/Category/ModuleCat/Sheaf`. Ten hits in PushforwardContinuous and ChangeOfRings,
  giving restriction-of-scalars ingredients, not this tensor normalization.
- LeanSearch: "Tensor extension along a ring sheaf isomorphism is naturally restriction
  along the inverse and sends pure tensors to the inverse scalar action". Eight hits:
  presheaf restriction, single-ring extension adjunction, tensor congruence and a
  polynomial equivalence. No exact arbitrary-site normalized comparison.
- `rg` across upstream `WeilConjectures` and side `lean/Sheaf` for
  `scalarExtension.*[Ii]so|changeOfRings.*[Ii]so|ringIsoTensor|<item id>` located
  single-ring/derived statements and topological-space specializations, including
  `InverseImageTensorPullbackComparison` and private `changeOfRingsIso` helpers. None
  has the arbitrary-site, arbitrary-module scope and two normalized formulas here.
- A separate `rg` for the new declaration names and the item id in
  `dag/lean_names_upstream.json`, upstream `WeilConjectures` and side `lean/Sheaf`
  returned no match. A follow-up search for existing change-of-rings pure-tensor/unit
  helpers found specialized topological helpers but no general independent-universe
  image of the unit on a local scalar tensor. The small helper here evaluates the
  existing unit directly, rather than replacing its construction.

Validation: the prescribed scompile wrapper checked the sandbox form and library
form. Its initial sole warning was a line over 100 characters; that line was wrapped.
The clean compile and the delivery preflight are run again after this correction.

## Second reading by Q15

This is the author's self-check under the direct-delivery brief, not an independent
review; the maintainer performs the independent reading. I reopened the current node,
its six proof steps and the completed module. I checked that the existential family
is shared between the two section equations and naturality, the inverse ring map has
direction S → R, and the pure-tensor helper uses the actual sheafification unit. I
checked the dependency's reversed factor convention against the Stacks definition
and verified that it changes neither formula. I also checked there is no arbitrary
comparison morphism hypothesis, no claim that all sheaf sections are pure tensors,
no hidden equality of site universes, no second module-category construction, and
no extra theorem with an unmatched DAG node. The line-length warning was repaired;
no mathematical clause changed.
