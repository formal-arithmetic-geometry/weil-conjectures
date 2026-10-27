## Worker report

The module states `SheafOfModules.scalarExtension_constraint_coherence`. Its only
postponed theorem is this node's theorem, with `sorry`; its docstring carries all seven
proof steps of the reviewed split. It supplies the small helper
`scalarExtensionConstraintTmul α H U h s`, defined in full as the module-sheafification
unit applied to `s ⊗ h` in the existing `changeOfRingsPresheaf`. This helper names a
section of the existing `changeOfRings`, and defines neither a replacement tensor nor
a replacement scalar-extension sheaf. The generalized helper
`scalarExtensionRingIsoTmul` instead has codomain `changeOfRingsOfUniverses`, whose
presheaf uses separately chosen restriction maps; it cannot be used definitionally
for the original `changeOfRings` interface used by the recorded monoidal declarations.

The structure `ScalarExtensionConstraintData A S α` packages the two comparison
isomorphisms and thirteen assertions below. The theorem states its `Nonempty`, so
it asserts exactly the existence of those comparisons with all the prescribed
properties. This structure packages this node's conclusions; it constructs no
new scalar extension, tensor, unit or coherence structure. Its two data fields
are `tensorIso` and `unitIso`; the remaining fields are proof obligations.

Every clause is rendered as follows (field names refer to the structure).

- A site small in the fixed module/ring universe: `{C : Type uC} [Category.{vC} C]`
  and `{J : GrothendieckTopology C}`, with rings and modules in `w` and
  `[EssentiallySmall.{w} C]`, exactly the node's smallness relative to coefficients. The sheafification, underlying-ring-sheaf
  instances are inferred for these sizes; there is no extra point,
  nonzero-ring or flatness assumption. The topology is the covering-sieve
  presentation used by the recorded site interface.
- Commutative ring sheaves and a unital ring-sheaf map:
  `(A S : Sheaf J CommRingCat.{w}) (α : A ⟶ S)`.
- Arbitrary A-module sheaves: all H, K, L, H₁ and K₁ range over
  `ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj A)`.
  The file writes the transparent helper `SheafOfModules.ScalarExtensionConstraintModules`
  abbreviation, whose body is exactly this `ringedSiteModules` expression.
- Scalar extension T(H): exactly `changeOfRings.{vC,uC,w} α H`, the sheafification
  of the presheaf `S(U) ⊗[A(U)] H(U)`. On morphisms T is the existing
  `changeOfRingsHom.{vC,uC,w} α H f`, sheafifying `id ⊗ f`.
- Tensors, associators, unitors: `⊗`, `⊗ₘ`, `α_`, `λ_`, `ρ_` and whiskerings
  use `cochainModulesMonoidal`, which is the existing localization construction
  `monoidalCategory` from the recorded tensor nodes. The unit `𝟙_` is the ring
  sheaf regarded as its own module.
- Local `h ⊗ k`: `scalarExtensionConstraintPureTensor.{uC,vC,w} A H K U h k` applies the module-sheafification
  adjunction unit to the presheaf pure tensor, then applies
  `(tensorObjIsoSheafification H K).inv.val.app U`. No surjectivity on sections
  of a sheafification unit is asserted or used.
- Existence and invertibility: the theorem asserts `Nonempty
  (ScalarExtensionConstraintData A S α)`; the fields `tensorIso` and `unitIso`
  are the comparison isomorphisms D and D₀. Their `hom` and `inv` are actual module-sheaf
  morphisms, so S-linearity, restriction compatibility and descent are built in.
- Field `insertion`: `(D H K).hom` sends `q_(H⊗K)(h ⊗ k)` to `q_H(h) ⊗ q_K(k)`
  on every U. Here `scalarExtensionConstraintTmul ... 1` is q.
- Field `unique`: every S-linear sheaf map d with precisely that generator formula
  equals `(D H K).hom`. Together with `insertion` this is the stated uniqueness.
- Field `natural`: `T(f ⊗ₘ g) ≫ D_(H₁,K₁) = D_(H,K) ≫ (T(f) ⊗ₘ T(g))` for
  arbitrary f and g, the natural-family assertion in both variables.
- Fields `unit_hom` and `unit_inv`: `D₀.hom` sends the sheafification image of `s ⊗ a` to
  `s * α(a)`, and `D₀.inv` sends s to the image of `s ⊗ 1`.
- Field `tensor_hom`: the forward tensor formula on `s ⊗ (h ⊗ k)`.
- Field `tensor_inv`: the inverse tensor formula on `(s ⊗ h) ⊗ (t ⊗ k)`, with
  coefficient `s * t` in its target.
- Field `oplax_associativity`: the full oplax associativity equation, with source
  `T((H ⊗ K) ⊗ L)` and target `TH ⊗ (TK ⊗ TL)`.
- Fields `oplax_left_unit` and `oplax_right_unit`: the left and right oplax unit equations with D₀ and
  the canonical unitors, respectively.
- Field `lax_associativity`: the lax associativity equation for the inverse constraints:
  `(D_HK.inv ▷ TL) ≫ D_(H⊗K,L).inv ≫ T(α_.hom)` equals
  `α_.hom ≫ (TH ◁ D_KL.inv) ≫ D_(H,K⊗L).inv`.
- Fields `lax_left_unit` and `lax_right_unit`: the left and right lax unit equations for D₀.inv and
  D.inv, with the canonical left and right unitors.
- Categorical composition `≫` is left-to-right, so every displayed composite
  is exactly the reverse order of the node's right-to-left `∘` display.

The return's H2 is repaired by dropping the theorem statement dependency
`lem-pur-sheaf-line-evaluation-inverse-pair` and its import. Its theorem was never
used. The two small helpers are now in the owning item module:
`ScalarExtensionConstraintModules` is transparent notation for the recorded
`ringedSiteModules`; `scalarExtensionConstraintPureTensor` spells out the recorded
module sheafification unit followed by `tensorObjIsoSheafification.inv`.
This is the item-module-helper option explicitly permitted by the return.
No new nodes or dependency modules are needed. The node now differs from the live
base only in `lean`; its original statement dependencies are restored.

Dependency declarations used and source signatures inspected:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the accompanying site convention
  retains Mathlib `GrothendieckTopology` and `Sheaf` for the sieve presentation.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`:
  `SheafOfModules.cochainModulesMonoidal`, which instantiates the original
  localization monoidal structure. Its public imports retain the independent-size
  tensor interface of the dependency node.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`; its public imports supply
  `monoidalCategory`, `tensorObjIsoSheafification`, `changeOfRingsPresheaf`,
  `changeOfRings` and `changeOfRingsHom` with their full signatures/docstrings.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`:
  `PresheafOfModules.sheafification` and `sheafificationAdjunction`.
- Proof imports: `TensorProduct`/`TensorProduct.lift`/`LinearMap.rTensor`
  (Mathlib tensor Basic and Map);
  `SheafOfModules.tensor_bilinear_universal`
  (`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`);
  `PresheafOfModules.existsUnique_bilinear_sheafification_extension`
  (`WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`);
  `SheafOfModules.restrictScalars`
  (`Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`).

Sources read: `literature/stacks-project/sites-modules.tex`, Section 03EK,
including the scalar-extension/associativity displays and the bilinear
sheafification hint of Tag 0GMW; the full seven-step reviewed node proof.

Edge cases checked mathematically before writing: identity coefficient map;
the point site with Z -> Z/nZ, including nonflat extension; zero target ring;
zero H or K; empty site and a site with an empty covering. All formulas still
type and reduce to the usual balanced tensor formulas or the unique zero map.
No step assumes that every section of a sheaf tensor is globally a pure tensor
or a global sum of such tensors. No statement correction or disputed clause.

Searches for an exact existing statement:

- `msearch.py ... leanfinder` query: "Extension of scalars along sheaves of
  commutative rings coherent tensor and unit comparisons with pure tensor formulas".
  Eight hits: module pullback unit morphisms and fixed-coefficient condensed
  monoidal structures; no exact arbitrary-ring-sheaf coherence theorem.
- `msearch.py ... loogle` query:
  "SheafOfModules.changeOfRings, CategoryTheory.Functor.OplaxMonoidal".
  Zero hits; the external index does not know the project's changeOfRings name.
- `msearch.py ... grep` query: "changeOfRings|extendScalars|[Oo]plax" in
  `Algebra/Category/ModuleCat/Sheaf`. One import hit in ChangeOfRings; no match.
- `rg` searches in both `lean/WeilConjectures` and `lean/Sheaf` for scalar
  extension, changeOfRings tensor/monoidal comparisons, and this blueprint id.
  Related comparison/cancellation and inverse-formula lemmas exist, but none
  contains the unique natural comparison, scalar unit formulas and all six
  coherence equations together. In particular
  `exists_changeOfRings_tensor_comparison` compares restriction of scalar
  extension with tensoring by the restricted ring; it is a different statement.
- Exact proposed declaration-name search in Mathlib, WeilConjectures, Sheaf and
  `dag/lean_names_upstream.json`: no collision.

Validation: per-file server compilation via scompile.py, followed by deliver2.py
preflight and compilation. The final outputs are recorded below after validation.

Elaboration details: site and coefficient universes are explicit; the small
helper names the existing scalar-extension unit so it is elaborated once.
Local irreducibility attributes prevent repeated expansion of scalar-extension
and localization tensor objects. These attributes add no declaration or
mathematical assumption and do not change the canonical monoidal structures.

Additional searches retained from the saved packet:

- `msearch.py leanfinder`: "Sheafified scalar extension along a morphism of
  sheaves of commutative rings has coherent tensor and unit constraints":
  eight hits on sheafification scalar-action laws, pullback/sheafification
  compatibility and forgetting module structures; no exact match.
- `msearch.py loogle`: "SheafOfModules, CategoryTheory.Functor.OplaxMonoidal":
  zero hits.
- `msearch.py grep`: "changeOfRings|scalarExtension" in
  Algebra/Category/ModuleCat/Sheaf: one ChangeOfRings import hit.
- `rg` for all three proposed names in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json: no collision.

The related `ScalarExtensionTensorCore` in ScalarExtensionBinaryCoherence
uses the separately constructed `changeOfRingsOfUniverses` and site tensor
functors and a separately specified `ScalarTensorCoherence`, with no inverse
formulas, uniqueness clause or lax equations in its interface. The present
package retains the recorded localization tensor, its actual canonical
associators/unitors and the original `changeOfRings`, and states all clauses.
It cannot be recorded as an exact existing match on that core theorem.

The initial single large existential conjunction exceeded the per-file limit.
Packaging the same conclusions in a structure avoids repeated elaboration of
the entire nested dependent conjunction. No limit was increased and no case
was removed. All universe parameters on scalar extension and pure tensors are
explicit, including in fields.

The initial packet passed the required resumed dry run (commit fa028003655);
that mechanical pass did not discharge the independent mathematical returns.
Final repaired-file validation is recorded below.


## Return repairs and self-check by Q48

H2: removed the line-evaluation theorem from `stmt_deps` and public imports.
Neither its theorem nor any chosen data from it appears in this module.
The two item helpers use the actual recorded module category, sheafification
adjunction and tensor comparison, with real bodies. All five declarations are
listed in `lean.declarations` and carry the item's source and blueprint marker.

H3/H9: the category is now `{C : Type uC} [Category.{vC} C]`, and both rings
and modules have independent universe `w`, with `[EssentiallySmall.{w} C]`.
The standard `[J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]`
instance records that forgetting commutative rings preserves sheaves; it is
available on every such site from preservation of the relevant limits. Every change-of-rings occurrence is
explicitly `.{vC,uC,w}`; all helper applications explicitly bind their
universe parameters. This is the `w` / `EssentiallySmall.{w}` interface explicitly
requested as an alternative by the return.
For the cited application on `X.ProEt`, take `uC = t+1`, `vC = t`, and `w = t+1`;
then the coefficient/module universe is `t+1`, exactly the site's `Ab.{t+1}`.
There is no equality imposed between `t` and `t+1`. At `uC=vC=w`, the signature
recovers every case of the old packet. No natural-language statement correction
is needed: this repairs the Lean restriction to match the already reviewed node.

Advisory H4: read `def-sfb-scalar-extension-pure-tensor-section` and
`scalarExtensionRingIsoTmul` in `ScalarExtensionRingIso`. Its codomain remains
`changeOfRingsOfUniverses`, defined with the independent chosen presheaf restriction
maps. The present item retains `changeOfRings`, the original recorded construction.
The two definitions are not definitionally identical as sheaves. Thus the small
`scalarExtensionConstraintTmul` helper continues to name the actual unit at the
item's presheaf, rather than silently changing T or assuming a comparison theorem.
Likewise `RingedTensor.pure` in `RingedTopoiTensorSections` has the returned
single-universe restriction, so it cannot supply the needed independent-size
helper without a separate interface repair. The return explicitly permits an
item helper, used here.

## Second reading by Q48

Self-check (no additional agent was started, as required by the dispatcher):
re-read the node and the file together, including the literal type of
`tensorObjIsoSheafification` and the independent-size binders of `changeOfRings`,
`changeOfRingsHom` and `cochainModulesMonoidal`. The thirteen assertions
`insertion`, `unique`, `natural`, `unit_hom`, `unit_inv`, `tensor_hom`, `tensor_inv`,
three `oplax_*` and three `lax_*` fields are unchanged except for explicit universe
parameters and helper names. Both isomorphism fields still have the same sources
and targets. The actual canonical associators and unitors and the left-to-right
composition order are preserved. All seven proof steps are retained verbatim.
The one postponed theorem is still `scalarExtension_constraint_coherence`.
Checked the identity map, nonflat Z to Z/n, zero target ring, zero modules,
empty site/empty covers again; the universe repair excludes none of these.
Searches of Mathlib/project/DAG names find no collision for the new helper names.
No new mathematical hypothesis, conclusion, object, or disputed statement.

Final validation: scompile.py exit 0 for the delivered module, library compilation
42.4 seconds with no errors or warnings. A separate module-mode scratch consumer
also compiled both as a sandbox (5.0 seconds) and at its library probe name
(7.8 seconds), exit 0 without warnings. It imports the repaired module and
Mathlib's pro-etale site and applies
`scalarExtension_constraint_coherence.{t+1,t,t+1}` to arbitrary
`A S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{t+1}` and `α : A ⟶ S`,
with no additional binders or assumptions. Thus the precise universe case named
in H3/H9 is type-checked, including inference of EssentiallySmall and the ring
forgetful sheaf-composition instance. The scratch consumer is not delivered.
The module retains one theorem with `sorry`, no proved theorem or hollow data.
Node comparison against the current read clone: only `lean` differs; its
`stmt_deps` exactly match the live node, with no spurious theorem dependency.
