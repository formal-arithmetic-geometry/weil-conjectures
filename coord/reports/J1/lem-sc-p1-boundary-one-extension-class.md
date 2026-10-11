## Worker report

The module `Sheaf.AlgebraicGeometry.BoundaryUnitExtensionClass` states
`AlgebraicGeometry.Scheme.Modules.boundary_unit_eq_extensionClass`, with proof `sorry`.
No definitions, new nodes, dependency replacements or statement corrections are needed.

Source read: Stacks Cohomology Tag 0B3A, label `lemma-h1-extensions`, statement and proof,
from the locally available source copy
`/home/ubuntu/weil-sandbox/E1/lem-sc-p1-ext-yoneda-functoriality/scratchpad/cohomology.tex`,
lines 345–392. The repository's literature directory does not contain the TeX checkout on
this machine. The source explicitly sends an extension of the structure sheaf to the
boundary of 1. The item's restriction from ringed spaces to schemes is unchanged.

Hypothesis and clause correspondence:

- Any scheme X: `{X : Scheme.{u}}`; u is explicitly declared. There are no finiteness,
  separatedness, smoothness or field assumptions.
- O_X-modules A and E: `(A E : X.Modules)`. O_X is the existing
  `SheafOfModules.unit X.ringCatSheaf`, the free sheaf of rank one.
- The short exact sequence 0 → A → E → O_X → 0: f and g have these exact sources and
  targets, `w : f ≫ g = 0` packages their composite into `ShortComplex.mk f g w`,
  and `hS : (ShortComplex.mk f g w).ShortExact` supplies exactness, mono f and epi g.
  This is categorical sheaf exactness, not surjectivity on global sections.
- Its Yoneda class e: `hS.extClass`. Naming the uniquely attached class directly avoids
  an extra binder with an equality to e. Mathlib ExtClass.lean defines this as the
  derived-category class of the short exact sequence.
- Ext as in def-sc-ext-sheaf: the source abbreviation `Scheme.Modules.Ext` is
  `Abelian.Ext` on X.Modules; `[HasExt.{u} X.Modules]` is the infrastructure parameter
  required by that recorded definition. It expresses small Ext groups and is available
  for scheme modules, not an additional geometric hypothesis.
- The canonical identification from lem-sc-ext-locally-free:
  `locallyFreeUnitExtAddEquivH A 1`, the recorded declaration for precisely the unit
  specialization Ext¹(O_X,A) ≃+ A.H 1. No arbitrary equivalence is quantified over.
- The connecting homomorphism H⁰(X,O_X) → H¹(X,A): `H.δ hS 0` from the existing source
  module Cohomology.LongExact. Its definition is postcomposition with the extension
  class of the forgotten short exact sequence in abelian sheaves; it is the connecting
  map of the covariant Ext long exact sequence. It is defined independently of the
  locally free comparison, so this assertion does not define the boundary by its RHS.
- The element 1: `((H.zeroLinearEquiv O).symm
  ((O.unitHomEquiv (𝟙 O)).val (op ⊤)))`, with O expanded everywhere in the file.
  Mathlib `SheafOfModules.unitHomEquiv_apply_coe` says the inner section at U is
  `(𝟙 O).val.app U (1 : X.ringCatSheaf.obj.obj U)`, hence exactly the unit section.
  `H.zeroLinearEquiv` transports it to H⁰. This avoids assuming a nonexistent One
  instance on the ModuleCat carrier of the unit sheaf's global sections.
- “Sends 1 to e under the identification”: the displayed equality has `H.δ hS 0`
  evaluated at that unit on the left and `locallyFreeUnitExtAddEquivH A 1 hS.extClass`
  on the right, both in A.H 1.

Dependency declarations read and used:

- `WeilConjectures.AlgebraicGeometry.Modules.Ext`,
  `AlgebraicGeometry.Scheme.Modules.Ext` (lines 45–52), recorded by def-sc-ext-sheaf;
  imported through the recorded comparison module.
- `Sheaf.AlgebraicGeometry.LocallyFreeExtCohomology`,
  `AlgebraicGeometry.Scheme.Modules.locallyFreeExtAddEquivH` and
  `locallyFreeUnitExtAddEquivH` (lines 89–112), recorded by lem-sc-ext-locally-free.
  Read its canonical comparison construction and proof docstrings in full.
- `WeilConjectures.AlgebraicGeometry.Cohomology.LongExact`, `H.δ`,
  `shortExact_map_toSheaf`, and `Cohomology.Exact`'s `toAb`: the pre-existing
  abelian-sheaf boundary, with the exactness instances for the scheme-module category.
- `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`, `H.zeroLinearEquiv` (243–248).
- Mathlib `SheafOfModules.unit`, `unitHomEquiv`, `unitHomEquiv_apply_coe`
  (Algebra/Category/ModuleCat/Sheaf.lean:173–184), and
  `ShortComplex.ShortExact.extClass` (DerivedCategory/Ext/ExtClass.lean:78–87).

The H encoding is the one explicitly used by the landed canonical comparison dependency.
It is abelian-sheaf cohomology, with the comparison to ringed-space module-derived
cohomology supplied at stage 3 as specified by the standing conventions. No second
cohomology definition or replacement of that dependency is introduced here.

Edge cases checked: the empty scheme is allowed (the unit section is then zero, both
cohomology groups vanish); A = 0 is allowed; split extensions give zero Yoneda class
and zero boundary; no characteristic restriction or nonzero-ring hypothesis occurs.
The source and target of the connecting map have degrees 0 and 1 exactly. No global
lift of 1 is assumed. All variables and universes are explicitly bound, and there is
no file-local notation or instance.

Searches actually run:

- msearch leanfinder: “The cohomology connecting homomorphism sends the unit section
  to the Yoneda extension class of a short exact sequence of sheaves of modules”.
  Eight hits, including `ShortComplex.ShortExact.extClass_hom` and group-cohomology
  boundary formulas; none states this canonical sheaf Ext/cohomology comparison.
- msearch loogle: `CategoryTheory.ShortComplex.ShortExact.extClass, Sheaf.H` returned
  no hits and reported unknown identifier Sheaf.H. Repeated with
  `CategoryTheory.ShortComplex.ShortExact.extClass`: twelve abstract Ext/class/exact
  sequence results, none the unit formula under locallyFreeUnitExtAddEquivH.
- msearch grep: `extClass|connecting` in CategoryTheory/Sites/SheafCohomology:
  two Mayer–Vietoris hits using an extension-class connecting map, not this theorem.
- msearch leansearch: “cohomology boundary of the unit section equals the extension
  class of a short exact sequence of modules over a ringed space”: unavailable,
  Internal Server Error, not treated as evidence of no match.
- rg of the item id in WeilConjectures: no hit. rg of `extClass|boundary.*unit` in
  its AlgebraicGeometry/Cohomology and Modules directories found the existing
  `H.δ` definition and its naturality/exactness, but no unit/comparison theorem.
- rg of `boundary.*unit|extensionClass|extClass` in lean/Sheaf/AlgebraicGeometry
  found Ext pushout/associativity statements, not this formula. Read the existing
  LocallyFreeExtCohomology module and used its canonical unit specialization.
- rg of the proposed declaration name and unit/boundary phrases in Mathlib, the
  source project, lean/Sheaf and dag/lean_names_upstream.json: no name collision
  and no exact theorem found.

Validation: server single-file compile succeeded cleanly in 1.8 seconds. Initial
elaboration exposed the scheme-category exactness instance wrapper and the absence
of One on the unit's global-section ModuleCat carrier; using the existing `H.δ` and
`unitHomEquiv` fixed both. No mathematical fault or STATEMENT-DISPUTED remains.

## Second reading by J1

I independently read the sandbox node and module, both statement dependencies' nodes
and recorded declarations, the full landed LocallyFreeExtCohomology module, and the
Stacks source at `lemma-h1-extensions` (Tag 0B3A), lines 345–392 of the local source
copy named above. The source assumes only a ringed space and a sheaf of modules;
the node specializes to schemes. There is no omitted ambient geometric assumption.
The node has no statement correction, new definition node, or dependency replacement.

Object/hypothesis/conclusion checklist, in the order of the node:

1. Scheme X: `{X : Scheme.{u}}`, with `universe u` explicitly declared. PASS: arbitrary
   scheme, with no field, Noetherian, separation, properness, or finiteness hypothesis.
2. O_X-modules A and E: `(A E : X.Modules)`. The quotient is exactly
   `SheafOfModules.unit X.ringCatSheaf`, Mathlib's free rank-one module whose underlying
   sheaf is O_X. I read `unit` and `unitHomEquiv` in Mathlib's ModuleCat/Sheaf. PASS.
3. Short exact sequence: `(f : A ⟶ E)` and
   `(g : E ⟶ SheafOfModules.unit X.ringCatSheaf)`, with `w : f ≫ g = 0` and
   `hS : (ShortComplex.mk f g w).ShortExact`. PASS: these are precisely the arrows and
   sheaf-category exactness, including the mono and epi conditions. No surjectivity
   on global sections or chosen lift of 1 is imposed. The witness w merely packages
   the zero composite already required by short exactness.
4. Yoneda class e in Ext¹(O_X,A): `hS.extClass`. I read Mathlib's Ext/ExtClass
   construction and `extClass_hom`: this is the class of the same short exact sequence
   in the derived category. PASS: the node introduces e as the attached class, so no
   independent class variable is needed. `Scheme.Modules.Ext` in the dependency's
   recorded upstream module is `Abelian.Ext` on X.Modules, not sheaf Ext.
5. Ext infrastructure: `[HasExt.{u} X.Modules]` is the same size parameter as the
   recorded Ext and comparison declarations. PASS: scheme module categories are
   Grothendieck abelian; `IsGrothendieckAbelian.hasExt` provides this small-Ext
   infrastructure. It is not a restriction on X or an assumption of finite Ext.
6. Canonical identification Ext¹(O_X,A) = H¹(X,A):
   `locallyFreeUnitExtAddEquivH A 1`. PASS: this is explicitly recorded among the
   lem-sc-ext-locally-free declarations. I read its construction from the exact
   internal-Hom functor, identity section, inverse dual evaluation, and tensor-unit
   isomorphism. The equality uses this actual canonical map, not an arbitrary chosen
   additive equivalence. Its codomain is A.H 1 as needed. The landed dependency uses
   the existing abelian-sheaf H encoding; the standing cohomology convention allows
   that encoding with the module-derived comparison at stage 3.
7. Connecting homomorphism H⁰(X,O_X) → H¹(X,A): `H.δ hS 0`. PASS: I read
   Cohomology/LongExact, including `shortExact_map_toSheaf`, and Cohomology/Exact's
   `toAb`. This is the boundary for the forgotten short exact sequence of abelian
   sheaves, by postcomposition with its class. Its definition does not use the
   locally-free comparison, so the proposed statement is not true by definition.
8. The element 1: `((H.zeroLinearEquiv O).symm
   ((O.unitHomEquiv (𝟙 O)).val (op ⊤)))`, with O expanded in the actual signature.
   PASS: `unitHomEquiv_apply_coe` evaluates this identity at the ring section 1,
   and `H.zeroLinearEquiv` (Cohomology/Defs) identifies H⁰ with global sections.
   Thus the expression is exactly the unit, with no nonexistent One instance on
   the global-sections ModuleCat carrier required.
9. Conclusion: the equality of `H.δ hS 0` applied to that unit with
   `locallyFreeUnitExtAddEquivH A 1 hS.extClass`. PASS: both sides are in A.H 1;
   the formula asserts exactly that 1 maps to the canonical image of e. There are
   no extra conclusions or reordered dependent choices.

Edge cases: the empty scheme and zero module A are included; neither an inhabited
space nor a nontrivial ring/module is assumed. On the empty scheme the unit section
is zero. A split extension gives the zero class and zero boundary. All characteristics
are allowed. Degrees are exactly 0 and 1, not a theorem restricted to positive input
degree. There is no indexing family, so empty-index cases do not arise. Scheme and
module universes follow the recorded dependency throughout, with no independent test
universe or unbound implicit variable. No file-local notation/instance is introduced.

Independent searches (different phrasing from the worker):

- msearch leanfinder: “first sheaf cohomology class obtained by applying connecting
  map to the constant unit section of an extension of the structure sheaf”. Eight
  hits: Sheaf.H and nonabelian H1/cocycle infrastructure, no boundary-of-unit theorem.
- msearch loogle: `SheafOfModules.unitHomEquiv`. Six hits: the section equivalence,
  its composition formulas, evaluation at 1, and free/pullback formulas; none states
  this Ext/cohomology compatibility. The evaluation lemma confirms item 8 above.
- msearch leansearch: “The boundary map on global sections sends one to the class in
  first cohomology corresponding to an extension of the structure sheaf”. Service
  unavailable (Internal Server Error); this is not evidence of absence.
- Independent rg on Mathlib's sheaf-cohomology/site directories, all upstream
  WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json, using
  `delta.*one|δ.*1|unit.*extClass|extClass.*unit|boundary.*(one|unit)|image of.*1`
  and the proposed declaration name. Related results are Kummer boundaries,
  Riemann–Roch's degree-zero section formulas, and abstract extension compositions;
  no duplicate of this canonical-comparison equality was found.

H5/H6/H8/H9: the delivery contains just one theorem with `:= sorry`, no definition
or proved helper. Both imports are used. The module and theorem docstrings give
Stacks 0B3A and the blueprint id. The proof docstring reproduces the node's two
steps: universal delta-functor compatibility, followed by the Ext connecting formula
and identity functoriality. Lines and explicitly bound variables were checked.
The node's lean.statement matches the file signature verbatim.

Mismatches found: none. Changes: appended this second-reading record only; the
correct Lean and node record were preserved. Server single-file compilation and
stage-2 delivery preflight are checked immediately after this report is written.
