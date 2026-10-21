## Worker report

The module `Sheaf.AlgebraicGeometry.InternalExtensionFinitePresentation` states
`AlgebraicGeometry.ProEtale.internalExtension_finitePresentation`, with `sorry` as its
entire proof. It states preservation of global finite presentations and the canonical
finite-free and cokernel comparisons requested in the node. No definition is added.
The item's natural-language statement, dependencies and proof plan are unchanged.

Source read: current blueprint main-20261015,
`sec-six-functors-basics/sk-thm-sfb-qlbar-two-colimit/lem-sfb-extend-to-qlbar-constructible.proof.md`,
final sentence about tensoring local finite presentations on strata. The DAG expands
this sentence into the five finite-free and cokernel calculation steps; all five are
included in the theorem docstring. The upstream `ModuleObjects.Free` definition
explicitly uses global finite-free cokernel presentations, as does this node; the
statement does not substitute Mathlib's locally finitely presented sheaf predicate.

Hypothesis and clause correspondence:

- The scheme is `(X : Scheme.{u})`, with its actual small pro-etale topology
  `Scheme.ProEt.topology X`. The ambient category is exactly
  `Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}`. Its site objects and morphisms retain
  their distinct universes; no equality of these universes is imposed.
- Ring objects R and S are objects of this sheaf category with `[MonObj R]` and
  `[MonObj S]`. Their stated commutativity is `[IsCommMonObj R] [IsCommMonObj S]`.
  `RingObjects.Ab` gives the tensor of abelian groups over the integers. The global
  sheaf monoidal instance in `GrothendieckAbelian.Monoidal.Defs` is
  `Sheaf.monoidalCategory`, just as the monoidal field of `sfbSheafTensorStructure`
  is; this is the sheafified objectwise tensor, with its integer-sheaf unit.
- The ring-object map is `(φ : R ⟶ S) [IsMonHom φ]`, with both multiplication and
  unit compatibility provided by the recorded Mathlib class.
- For every internal module M, the first conjunct quantifies
  `M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R` and assumes exactly
  `Mod.IsFinitelyPresented R M`. Its conclusion is
  `Mod.IsFinitelyPresented S ((Mod.extendScalars φ).obj M)`.
- The functor is the recorded `Mod.extendScalars φ`, whose real definition is the
  balanced bimodule coequalizer with its induced S-action; no arbitrary functor or
  alternative scalar extension is introduced.
- The second conjunct supplies a regular-module isomorphism e₀, normalized by
  `Mod.extendπ φ (Mod.regular R) ≫ e₀.hom.hom = S ◁ φ ≫ μ[S]`.
  This is the rank-one balanced-tensor comparison in proof step 2. The quotient is
  epi, so the equation uniquely specifies its forward map and hence its inverse.
- The family `e : ∀ k : ℕ, E.obj (Mod.finiteFree R k) ≅ Mod.finiteFree S k`
  supplies the comparisons for every rank, including zero. The displayed equation
  `E.map (biproduct.ι ... i) ≫ (e k).hom = e₀.hom ≫ biproduct.ι ... i`
  specifies their canonical normalization on all coproduct injections. These
  equations determine the maps uniquely by preservation of finite coproducts.
- For every pair of ranks m,n and every module map
  `f : Mod.finiteFree R m ⟶ Mod.finiteFree R n`, its scalar conjugate is written
  explicitly as `(e m).inv ≫ E.map f ≫ (e n).hom`, with Lean's left-to-right
  composition. The existential isomorphism c identifies `E.obj (cokernel f)`
  with the cokernel of that exact conjugate. Its compatibility with cokernel
  arrows is `E.map (cokernel.π f) ≫ c.hom = (e n).hom ≫ cokernel.π ...`.
  Thus it is the canonical cokernel comparison, not just an arbitrary isomorphism.
- Finally, for every module M and every given `_p : M ≅ cokernel f`, the statement
  gives `Nonempty (E.obj M ≅ cokernel ...)` for the same conjugated map. The
  intended isomorphism is `E.mapIso _p ≪≫ c`; its existence is exactly the node's
  displayed presentation of scalar extension. The `_p` name avoids an unused
  binder warning while retaining every presentation as a hypothesis.
- No flatness hypothesis, kernel-preservation hypothesis, finiteness of the
  scheme, nonemptiness of X, or nonzero-ring hypothesis is imposed.

Dependency declarations used, with full source signatures and docstrings inspected:

- `sk-def-sfb-sheaf-tensor`: `Sheaf.CategoryTheory.SheafTensor`,
  `CategoryTheory.sfbSheafTensor_properties` and the imported
  `CategoryTheory.sfbSheafTensorStructure`; its monoidal field is exactly
  `Sheaf.monoidalCategory J A`. `GrothendieckAbelian.Monoidal.TensorColimits`
  provides the corresponding global pro-etale instances and colimit preservation.
- `sk-def-sfb-ring-object`:
  `WeilConjectures.CategoryTheory.RingObjects.RingPresheaf`, importing
  `RingObjects.Ab` and Mathlib's `MonObj`, `IsCommMonObj`, `IsMonHom`. The
  recorded `Functor.monObjCompForget₂` is the presheaf specialization of those
  same classes; the theorem uses their general internal forms directly.
- `def-sfb-finitely-presented-module`:
  `WeilConjectures.CategoryTheory.ModuleObjects.Free`,
  `CategoryTheory.Mod.IsFinitelyPresented`, `CategoryTheory.Mod.finiteFree`.
  The exact existing definition is attached in this delivery; see below.
- `sk-def-sfb-change-of-scalars`:
  `WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`,
  `CategoryTheory.Mod.extendScalars` and `CategoryTheory.Mod.extendπ`.
- `sk-def-sfb-module-objects`: `Mathlib.CategoryTheory.Monoidal.Mod`,
  `CategoryTheory.Mod`, `Mod.regular`, and its action-compatible `Mod.Hom`.
  This module is publicly imported through the upstream dependencies.

Proof-only imports cover the stated proof dependencies:
`ModuleObjects.ChangeOfScalarsSquare` for
`Mod.preservesFiniteColimits_extendScalars` (also the recorded declaration of
`lem-sfb-modobj-extension-right-exact`);
`Mathlib.CategoryTheory.Monoidal.Bimod` for `Bimod.rightUnitorBimod`;
`Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` for
`CategoryTheory.rightExactFunctor_le_additiveFunctor`.
The generic extension node `def-sfb-modobj-extension` has a closed upstream audit
identifying the same `Mod.extendScalars`; its source is imported publicly already.
The abelianness infrastructure of `lem-sfb-modobj-abelian` is imported through
`ModuleObjects.Free`. `lem-sfb-grothendieck-sheafification` has no recorded module
or upstream audit declaration to import; the already imported upstream sheaf
infrastructure supplies the ambient abelian instance without a new hypothesis.

Edge cases checked before drafting: k=0 yields the initial/zero module and has
no injections to check; preservation of that coproduct fixes its unique map.
For m=0 the result is a finite-free presentation with no relations. For n=0 the
cokernel is zero. For φ=id the comparisons recover the usual identifications;
for S=0 every extension is zero. The empty scheme is allowed. The non-flat
map of constant rings Z → Z/2 causes no problem: only finite colimits, not
kernels, are preserved in the argument. No statement fault or disputed clause
was found.

Searches actually run:

- `msearch.py`, leanfinder: "Extension of scalars of internal modules preserves
  finite free cokernel presentations with canonical isomorphisms". Eight hits,
  all ordinary module presentation or localization results, including
  `FinitePresentation.of_isBaseChange`; no exact internal sheaf result.
- `msearch.py`, loogle: `"extendScalars", "FinitePresentation"`. Four hits,
  all `Module.FinitePresentation` localization comparison declarations.
- `msearch.py`, grep in CategoryTheory:
  `extendScalars.*[Ff]inite|[Ff]inite.*extendScalars|IsFinitelyPresented`.
  Zero hits in Mathlib's general category-theory tree.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `finitelyPresented|IsFinitelyPresented|extendScalarsRegularIso|fp_extend|internal_extension|internalExtension|internal-extension-finite-presentation`.
  Found the exact upstream finite-presentation definition and
  `AlgebraicGeometry.ProEtale.fp_extend` in
  `Sheaf.AlgebraicGeometry.BoundedConstructibleExtendScalars`. Read that module:
  `fp_extend` states preservation alone; its regular comparison is private, and
  it exposes neither the family of canonical comparisons nor the normalized
  cokernel isomorphisms required here. Thus it is not an exact binding for this
  stronger node. No matching complete statement was found.
- `rg` for the node identifier in `lean/WeilConjectures`: no hits.

Validation: the delivered theorem compiled cleanly via the prescribed server
`scompile.py`, both as a sandbox module and at its intended library module name
(3.3 and 3.1 seconds respectively). The existing-definition binding is also
checked by the delivery wrapper's server probe. No proof is supplied in stage 2.

## Dependency modules

`def-sfb-finitely-presented-module`: no new module is needed. This node had no
`lean` record, but its exact definition already exists in the upstream module
`WeilConjectures.CategoryTheory.ModuleObjects.Free`. The dependency copy changes
only `lean`, with `existing: true` and a note explaining the repair. Its
`finiteFree R n` is the finite biproduct indexed by `Fin n` of the regular module,
and `IsFinitelyPresented R M` is existence of n,m,f and a nonempty isomorphism
`M ≅ cokernel f`, under exactly the node's abelian, monoidal-preadditive and
right-exact tensor assumptions. This attaches the existing construction rather
than introducing a duplicate definition. All other dependency fields are kept.

## Second reading by Q09

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
