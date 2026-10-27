## Worker report

The single module `Sheaf.CategoryTheory.GeometricConstantLeftScalarExtension` states the two
natural comparisons, with sorry proofs, and owns the eight helper definitions in namespace
`CategoryTheory.ConstantLeftScalarExtension`. All eight helpers are listed in the item's
`lean.declarations`. There is no statement correction, new node, or dependency-record change.
The live record of `def-pod-ring-scalar-extension` is restored byte-identically, retaining
its original universe-general, stage-3-proved upstream declaration and declaration list.
All helper data are constructed from the existing upstream scalar extension and Mathlib
module sheafification; they specialize those constructions for this item.
The source read was Stacks sites-modules.tex, lemma-adjointness-tensor-restrict (03CZ),
lines 932–961, with its sectionwise-adjunction and sheafification argument. The current
blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability direct-images proof was also read;
this item is an auxiliary calculation for its open-direct-image argument, not the unit statement.

Hypotheses and clauses:

- Small sites are `{C D : Type u} [SmallCategory C] [SmallCategory D]` with topologies
  `J`, `K`. The common bound u is the small-site/coefficient bound used by the recorded
  inverse-image interface; independent derived-localization universe w is retained.
  `HasWeakSheafify … RingCat` supplies precisely the constant-ring sheafification required
  by that interface; module and abelian sheafification exist for these small sites.
- The geometric morphism is exactly `L`, `G`, `adj : L ⊣ G`,
  `hL : PreservesFiniteLimits L`. No presenting site functor or terminal site object is used.
- The rings are `{R S : Type u} [Ring R] [Ring S]` and the unital map is `a : R →+* S`.
  There is no CommRing assumption.
- The normalized canonical lifts are the recorded `ConstantLeftModuleInverseImageData`
  parameters `dR` and `dS`, including their given geometric adjunction and hL. The dependency
  theorem supplies these for every geometric morphism; this is a statement for any such
  normalized presentations rather than a choice of an unrelated module functor.
- `extension J a` and `extension K a` are the sectionwise balanced scalar extensions followed
  by actual module sheafification. Their domain and codomain are the dependency's `Modules`,
  transparently `ringedSiteModules` over `constantSheaf … RingCat`.
- The first conclusion is a natural isomorphism
  `extension J a ⋙ dS.moduleFunctor ≅ dR.moduleFunctor ⋙ extension K a` in exactly the
  direction L_S E_C → E_D L_R. A functor isomorphism includes naturality in M.
- For every M and every s, the set-sheaf maps t and t' are required to take each section m
  to `tensorSection … s m`. These maps are not arbitrary: the two universal quantifiers
  over site objects and sections specify them completely. The equation
  `L.map t ≫ dS.moduleSetIso.inv.app … ≫ (W K S).map (c.hom.app M) =
   dR.moduleSetIso.inv.app M ≫ t'`
  is precisely the geometric pure-tensor formula on underlying sheaves. It transports local
  sections by the actual functor L and its normalized comparisons, equivalently by the
  original adjunction unit. It makes no pointwise claim about L of a local section.
  All target maps c are morphisms of left S-module sheaves, so this also agrees with the
  scalar identification supplied by the normalized lifts.
- The second conclusion is a natural isomorphism
  `ModuleCat.ringExtendScalars a ⋙ constant J S ≅ constant J R ⋙ extension J a`.
  Its component at every Q is exactly the constant-sheaf comparison in the node; naturality
  in Q is part of the isomorphism of functors.
- Its equality quantifies over Q, T, s, q and sends the sheafification-unit image
  `constantSection J … T (ModuleCat.ringExtensionTmul a Q s q)` to
  `tensorSection J a (constant Q) T s (constantSection J Q T q)`.
  Thus both occurrences of constant sections and the extension sheafification unit are
  explicit, including the pure tensor, not just an unspecified isomorphism.
- Neither theorem assumes flatness, finiteness, a nonzero ring, a nonzero module or a point.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`, `Precoverage.IsSiteForCoverings`: the site
  convention is represented here by Grothendieck topologies, as in the lift dependency.
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`, `constantSheaf`: sheafification of the
  constant presheaf; constant module helper uses the corresponding module sheafification.
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`,
  `constant_left_module_inverse_image`, `ConstantLeftModuleInverseImageData`: the canonical
  normalized lifts; its imported transport module supplies `Modules`, `W`, and all the
  underlying-sheaf/adjunction normalizations. The full structure and docstrings were read.
- `Sheaf.CategoryTheory.ConstantLeftModuleTransport`,
  `ConstantLeftModuleInverseImageLift`, `constantLeftModuleTransport`: proof dependency and
  the underlying exact scalar transport used by the imported inverse-image data.
- `WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension`,
  `ModuleCat.ringExtendScalars`, `ringExtendScalarsAdj`, `ringExtensionTmul`,
  `ringExtensionComp`, `Sheaf.ringExtendScalars`: the original ordinary arbitrary-ring data
  remain imported from their upstream module and are not copied.
- `Sheaf.CategoryTheory.RingedSiteModules`, `ringedSiteModules`: the actual Mathlib
  `SheafOfModules` category; retained through `Modules`.
- `Mathlib.CategoryTheory.Sites.Sheafification`, `presheafToSheaf`, `toSheafify`,
  `sheafificationAdjunction`: explicit underlying abelian sheafification and units.
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
  `PresheafOfModules.sheafification`: equips the actual sheafified abelian sections with
  the sheafified-ring action. It is used by the item's helpers, not reimplemented.
- `Mathlib.CategoryTheory.Yoneda`, `Coyoneda.fullyFaithful`: proof-only import for the
  recorded co-Yoneda dependency. Its full declaration and the ext interface were read.
- `def-weil-size-convention` is metatheoretic and has no declaration or import.

Edge cases checked mathematically against the constructions: the empty site (there is no
section quantifier to fill and the maps are still sheaf maps); a nonempty site lacking a
terminal object; the zero ring S; Q = 0; identity ring maps; the nonflat map Z → Z/2;
and noncommutative rings such as matrix rings. The balanced tensor uses the arbitrary-ring
adjoint, not Mathlib's commutative TensorProduct. In all these cases the two formulas are
unit and S-linearity identities, so none requires exactness of scalar extension.

Searches before writing:

- msearch.py leanfinder: “Geometric inverse image commutes with extension of scalars of
  sheaves of left modules over arbitrary rings”, eight hits including
  `SheafOfModules.pullbackObjFreeIso` and `freeFunctorCompPullbackIso`; these concern free
  objects and presenting continuous site functors, not this arbitrary geometric morphism.
- msearch.py loogle: `"SheafOfModules", "restrictScalars"`, twelve hits for module-presheaf
  scalar restriction, not the two normalized comparisons.
- msearch.py grep: `constant.*[Ee]quiv|ringExtendScalars` in Algebra/Category/ModuleCat,
  no matches. Direct source reads located the existing upstream arbitrary-ring extension.
- rg in lean/WeilConjectures for the item id: none. Broad rg for ringExtendScalars and
  constant/equivalence located the upstream scalar construction and constant-section
  adjunct material, no existing statement of both comparisons.
- rg in lean/Sheaf located ConstantRingModuleSheaves and ConstantScalarGeometricAdjunctions;
  their full interfaces were inspected. The former requires CommRing, and the latter
  also treats commutative fixed-scalar lifts, so neither covers this node's arbitrary rings.
- The upstream declaration-name index was searched for the item and prospective names;
  no conflicting declaration was found. The new helper names live in
  `CategoryTheory.ConstantLeftScalarExtension` and the new theorem names were searched
  in both project Lean trees.

Validation: the repaired single item module is compiled by scompile.py against the
published live server library. Only the two named theorem proofs are sorry; every helper
definition has genuine data. Both theorem declarations, including their signatures and
proofs, were compared byte-for-byte before and after moving the helpers and are unchanged.

## Repair of returned head d37d67844cf8

H13/H4: the previous delivery incorrectly replaced the landed `def-pod-ring-scalar-extension`
record by a specialized interface. The repair restores its node file byte-identically to
live, including the existing `ModuleCat.restrictScalars_has_leftAdjoint` entry; no dependency
record is being updated or stale entry removed. The upstream module remains imported as
`WeilConjectures.Algebra.Category.ModuleCat.RingScalarExtension`.

All eight helpers (`presheafModules`, `sections`, `sheafification`, `constant`,
`tensorPresheaf`, `extension`, `tensorSection`, `constantSection`) were moved into the item
module without changing their data or names. Their docstrings now cite the item blueprint
id, and the item's `lean.declarations` lists every helper and both theorems. The separate
helper module was removed from the sandbox. The two item theorem declarations are
byte-identical to the reviewed delivery. This follows the maintainer's authorized option
of keeping the helpers in the owning item module; no new definition node is necessary.

The helpers provide only the constant-ring specialization needed for the item: `sections`
restricts the ring-sheaf action along the constant-ring unit; `tensorPresheaf` applies the
original `ModuleCat.ringExtendScalars` sectionwise; `sheafification` uses Mathlib's actual
`PresheafOfModules.sheafification`; `extension` composes these. `constant`, `tensorSection`
and `constantSection` name the objects and units used in the two formulas. The general
arbitrary-ring construction, composite comparison, and proved upstream interface remain
owned by the existing dependency and are used through imports.

## Second reading by NR

Author self-check for direct worker delivery; the independent reading is the maintainer's.
I reopened the node and the merged item module. The first natural isomorphism has domain L_S E_C
and codomain E_D L_R. The last map equality is well typed from L|M| to |E_D L_R M|;
t and t' are forced at all sections to be the sheafified pure-tensor maps. The second
natural isomorphism has the node's direction from the constant sheaf of the ordinary
balanced tensor, and its formula explicitly uses both sheafification units. Rings remain
noncommutative and modules are left modules in all constructions. The original scalar
extension is imported rather than copied; the item-owned helpers specialize it for the
constant-ring-sheaf formulas. The dependency record is identical to the live record. The two theorem proofs are sorry. In the original delivery, compiler feedback led
to correcting naturality binders and using the actual underlying presheaf of the module
sheafification in the unit definitions, with no mathematical statement change.
