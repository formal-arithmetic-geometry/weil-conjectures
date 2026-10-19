## Worker report

The whole item is already stated in
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`:
`AlgebraicGeometry.ProEtale.isIso_η_pointUpperStar` (line 259 of the supplied
framework source). Record `existing: true`; no module is written and no proof is changed.
The accompanying existing instances `laxMonoidal_pointLowerStar` and
`oplaxMonoidal_pointUpperStar` render the two structure clauses. Their names are included
in `lean.declarations`. The primary statement, verbatim through the signature, is:

```lean
instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u})
```

The framework source was read at
`lean/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Basic.lean`, including its complete
module docstring and the declarations at lines 153–268; `scompile.py --source
WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic` independently returned the
published source. The framework provenance and its unchanged open proofs are documented
in `coord/pefw-upstream-framework.md`. `branch: slopmaster2` identifies the upstream
framework, as in the existing binding for `lem-sfb-lc-weakly-etale`; this framework is
provided through the side overlay, not through the older local source checkout.

Clause-by-clause correspondence:

- The source site `*_proét` is `Profinite.{u}` with `coherentTopology Profinite.{u}`.
  The target is `Scheme.ProEt.topology specZ.{u}`. Both value categories are `Ab.{u + 1}`.
  `specZ` is `Spec (CommRingCat.of (ULift.{u} ℤ))`, the universe-lifted integer spectrum.
  There are no further mathematical hypotheses.
- The functor `u(S) = Spec LC(S, ℤ)` is `profiniteToProEt`: its underlying scheme is
  definitionally `Spec (.of (LocallyConstant S ℤ))`. Its direct image `pointLowerStar`
  is `profiniteToProEt.sheafPushforwardContinuous`, and `pointUpperStar` is precisely
  the underlying-presheaf inclusion followed by `profiniteToProEt.op.lan` and
  `presheafToSheaf`, as required by the dependency definitions.
- The tensor products are the localized monoidal structures `Sheaf.monoidalCategory`.
  On the pro-étale side this follows from
  `GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` and
  `ProEtale.sheafMonoidalCategory`; on the profinite side it is the coherent-site
  sheaf tensor supplied by the imported condensed framework. These use the ordinary
  `Ab` tensor over the integers. The recorded dependency's `sfbSheafTensorStructure`
  also sets its `monoidal` field to `Sheaf.monoidalCategory J A`; this is the same
  localization tensor, not a second construction. Its unit is sheafification of the
  constant presheaf with value the coefficient tensor unit, hence the constant integer
  sheaf, as stated by `sfbSheafTensor_properties`.
- The sentence that `p_*` is lax monoidal is
  `laxMonoidal_pointLowerStar : pointLowerStar.{u}.LaxMonoidal`.
- The specified adjunction is `pointUpperStarLowerStarAdjunction`, whose body is exactly
  the dependency's `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`
  specialized to `profiniteToProEt`, `Ab.{u + 1}`, and the two topologies. Mathlib's
  full declaration and docstring were read in `CategoryTheory/Sites/Pullback.lean`.
- The transferred oplax structure is `oplaxMonoidal_pointUpperStar`, whose body is
  exactly `pointUpperStarLowerStarAdjunction.leftAdjointOplaxMonoidal`.
  The definition of `Adjunction.leftAdjointOplaxMonoidal` was read: its `η` is the
  inverse Hom equivalence applied to the lax unit `ε pointLowerStar`. Thus it is the
  actual canonical mate required in the node, with direction `p^*ℤ ⟶ ℤ`.
- The last clause is `IsIso (Functor.OplaxMonoidal.η pointUpperStar.{u})`, exactly the
  existing primary instance. It asserts invertibility of this morphism, rather than
  mere existence of an isomorphism between the two objects.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SheafTensor`:
  `CategoryTheory.sfbSheafTensor_properties`, and its underlying construction
  `CategoryTheory.sfbSheafTensorStructure` in `Sheaf.CategoryTheory.SheafTensorStructure`.
  Both full signatures and docstrings were read, including the canonical comparison.
- `Mathlib.CategoryTheory.Sites.Pullback`:
  `CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`.
  The dependency is a Mathlib leaf and needs no new binding or specialization module.

Edge cases checked: the statement has no element, nonempty-site, or nonzero-sheaf
hypotheses. It includes the empty profinite set (whose locally constant ring is the
zero ring and whose spectrum is empty), as well as the terminal singleton. The unit
is the constant integer sheaf, not the zero sheaf or a cartesian terminal object.
The site morphisms remain in universe `u`, site objects in `u + 1`, and coefficients
in `Ab.{u + 1}`; no site universe equality or size restriction was added. The only
universe parameter of the primary instance is explicitly declared `universe u` in
its source. The local side copy has a `sorry` proof. The second reading below records the newer
published proof returned by `scompile.py --source`; neither observation alone certifies
its transitive axiom closure.

Searches:

- `msearch.py leanfinder`, query “The inverse image from condensed abelian groups to
  pro etale sheaves preserves the tensor unit”: eight Mathlib hits (condensed free
  abelian groups, light condensed tensor/sheafification, underlying functors); no
  whole-item match.
- `msearch.py loogle`, query
  `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal, CategoryTheory.Functor.OplaxMonoidal.η`:
  found `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_η`, the generic mate formula.
- `msearch.py grep`, query
  `leftAdjointOplaxMonoidal|sheafPushforward.*[Mm]onoidal|pullbackObjUnitToUnit`,
  subdirectory `CategoryTheory`: six hits in Mathlib monoidal functors and sites;
  generic interfaces only.
- `rg` of `pointUpperStar|pointLowerStar|profiniteToPro|isIso_η_pointUpperStar` in the
  project Lean, supplied framework, and old upstream source: the supplied framework
  contains the exact primary instance and the specified lax/oplax structures.
  Project consumers use the same point functors; no duplicate statement is needed.
- `rg` of the item id and declaration name in `dag/lean_names_upstream.json`, old
  upstream `WeilConjectures`, and `lean/Sheaf`: no old-checkout primary declaration;
  this is explained by the documented framework import, whose exact source was read.
- Read Mathlib `Sites/Monoidal.lean`, upstream
  `CategoryTheory/GrothendieckAbelian/Monoidal/Defs.lean`, and
  `Mathlib/CategoryTheory/Sites/Monoidal.lean` to verify the actual tensor and mate
  construction rather than inferring it from the instance name.

No statement fault or dispute, new node, or dependency replacement was found.
The required dry run checks all three recorded existing declarations through a compiled
probe and runs server preflight. The second reader supplies the independent reading.

## Second reading by Q11

Read independently on 2026-10-17: the complete delivered node and its seven proof
steps; its blueprint statement and proof at
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-def-sfb-pullback-from-point/lem-sfb-point-upper-star-unit.md`
and `.proof.md`; the parent `_section.md`; both direct statement dependencies;
the point-functor dependency records; the actual framework module; and the current
published module returned by `scompile.py --source`. There is no repair note for
this item. The source is the blueprint, rather than a Stacks statement with hidden
standing hypotheses. The parent explicitly fixes the profinite coherent site,
the small pro-etale site and the functor S ↦ Spec LC(S,Z).

The node's objects, hypotheses and conclusions, matched individually:

1. Source category Sh(*_proet,Ab):
   `Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}` in the full type of
   `pointUpperStar` and `pointLowerStar`. Verdict: exact, including coherent covers.
2. Target category Sh((Spec Z)_proet,Ab):
   `Sheaf (Scheme.ProEt.topology specZ.{u}) Ab.{u + 1}`. The definition
   `specZ := Spec (.of (ULift.{u} ℤ))` represents the integer spectrum at arbitrary
   scheme universe. Verdict: exact.
3. Tensor products and constant integer units as in `sk-def-sfb-sheaf-tensor`:
   read `sfbSheafTensor_properties`, `sfbSheafTensor_comparison` and
   `sfbSheafTensorStructure` in their recorded modules. The construction's
   `monoidal` field is `Sheaf.monoidalCategory J A`. The framework instances
   `GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall` and
   `ProEtale.sheafMonoidalCategory` use this same localization tensor.
   `sfbSheafTensor_properties` identifies its unit with
   `(constantSheaf J A).obj (𝟙_ A)`; for Ab this is the constant integer sheaf.
   Verdict: the specified tensor over Z, with the correct unit.
4. The specified p_* and its lax structure:
   `pointLowerStar` is restriction along `profiniteToProEt`, which is constructed
   from locally constant integer functions and contravariant spectrum.
   `laxMonoidal_pointLowerStar : pointLowerStar.{u}.LaxMonoidal` unfolds this
   functor and uses `sheafPushforwardContinuousLaxMonoidal`. Read that construction
   in upstream `Mathlib/CategoryTheory/Sites/Monoidal.lean`: it transports the lax
   structure from inclusion, restriction and sheafification along the inverse
   sheafification counit. Its `ε_sheafToPresheaf_app_comp_ε_sheafPushforwardContinuous_app`
   gives exactly the restriction/sheafification unit equation of node proof step 2.
   Verdict: canonical lax structure, with no extra assumption.
5. The specified p^* and adjunction:
   `pointUpperStar` is `Functor.sheafPullbackConstruction.sheafPullback` at the
   above functor, sites and coefficients. Read Mathlib Sites/Pullback lines 42–78:
   its body is `sheafToPresheaf J A ⋙ G.op.lan ⋙ presheafToSheaf K A`.
   `pointUpperStarLowerStarAdjunction` uses the dependency's exact recorded
   `sheafAdjunctionContinuous`, constructed by composing the Kan/sheafification
   adjunctions and restricting fully faithfully. Verdict: the actual dependency
   adjunction, with independent site object and morphism universes retained.
6. Transferred oplax structure:
   `oplaxMonoidal_pointUpperStar :=
   pointUpperStarLowerStarAdjunction.leftAdjointOplaxMonoidal`.
   Read Mathlib Monoidal/Functor lines 1058–1074: its unit is
   `(adj.homEquiv _ _).symm (ε G)`. Verdict: precisely the mate prescribed by
   the node, with direction p^*Z → Z.
7. That particular unit comparison is invertible:
   `instance isIso_η_pointUpperStar : IsIso (η pointUpperStar.{u})`.
   The namespace opens `Functor.OplaxMonoidal`, so this is its `η`.
   Verdict: exact final clause; all three clauses are carried by the three
   recorded declarations, without a stronger tensor-comparison clause.
8. Additional hypotheses: none. All prerequisites for continuity, Kan extension,
   sheafification and the coefficient/site structures are supplied internally
   by the established framework. No extra field, finiteness, Noetherian,
   nonempty, or characteristic assumption is present. Verdict: exact.

Edge cases: empty profinite sets are allowed and give the zero ring LC(empty,Z)
and empty spectrum. The singleton is allowed and supplies the terminal test
object in the proof. There is no arbitrary scheme or index set binder to restrict;
the fixed site includes the empty scheme. Zero abelian sheaves are included in
the categorical structures, while the specified tensor unit is Z. There is no
n or characteristic binder. `universe u` is bound explicitly; site objects have
universe u+1, morphisms u, and coefficients Ab.{u+1}, as prescribed by the
project's size convention. No independent universe is silently equated.

Independent searches, using wording different from the first worker:

- `msearch.py leanfinder`: “A geometric inverse image functor between abelian
  sheaves sends the sheafified constant integer tensor unit to the unit by its
  canonical oplax map”. Eight hits, including module-sheaf pullback unit maps and
  the cartesian inclusion unit. These use different categories or tensor; none
  replaces the exact existing point-functor declaration.
- `msearch.py loogle`: the initial combined query with unqualified `IsIso` was
  rejected by the service as an unknown identifier. Repeated with the qualified
  `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal_η`; found the exact generic
  mate formula, whose defining source was then read.
- `msearch.py grep`: `isIso_η|sheafPushforward.*LaxMonoidal|leftAdjointOplaxMonoidal_η`
  in CategoryTheory returned the generic mate API. Direct `rg` searches for
  `pointUpperStar|pointLowerStar|isIso_η_point` covered project Sheaf sources,
  old upstream WeilConjectures and the supplied framework. They confirm the
  existing exact declaration and project consumers using these same functors.
  The more general upstream `isIso_η_sheafPullback` was also opened; it concerns
  the same canonical mate and explains the current published instance proof.

No H3/H4 mismatch, missing notion, dependency repair or statement correction
is needed. No new node or module is delivered, so the new-node and new-docstring
requirements do not apply to this existing-source binding. No live source or
proof was changed. The node retains its complete seven-step natural-language
proof for later work.

One stale documentation claim was repaired: the local framework copy's primary
instance has a `sorry`, but the current published source has
`by unfold pointUpperStar; infer_instance` with the identical signature and
canonical oplax structure. Updated the worker report and `lean.note` to distinguish
these sources and avoid claiming the current proof is still `sorry`. Proof closure
is not inferred from the successful type check. The node's `lean.statement` is
verbatim the existing signature. The delivery dry run checks all three existing
names through its compiled probe; there are no delivered Lean files to compile.
