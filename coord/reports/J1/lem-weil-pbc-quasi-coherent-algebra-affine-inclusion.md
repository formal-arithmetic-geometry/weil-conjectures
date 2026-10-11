## Worker report

Module: `Sheaf.AlgebraicGeometry.QuasiCoherentAlgebraAffineInclusion`.
Declaration: `AlgebraicGeometry.quasi_coherent_algebra_affine_inclusion`.
This is one theorem with a `sorry` proof; no new definition or proof was introduced.
Its source is [Stacks 01LN](https://stacks.math.columbia.edu/tag/01LN) and
[Stacks 01LO](https://stacks.math.columbia.edu/tag/01LO), read online because the
literature sources are not installed in this remote clone. Both agree with the node.
No statement correction or dispute is needed.

Hypothesis and clause correspondence:

- Scheme S: `(S : Scheme.{u})`.
- Sheaf of commutative O_S-algebras: `(A : S.CommAlgebraSheaf)`, the existing
  `Under S.sheaf` encoding. Its ring sheaf is `A.right` and the structure map is `A.hom`.
- Quasi-coherence of the underlying module: `(hA : A.toModule.IsQuasicoherent)`.
  This is the Mathlib predicate explicitly specified for the quasi-coherent clause of
  `pqf-def-coherent` in its module docstring. Its main recorded declaration, `IsCoherent`,
  is the separate coherent clause and is not the predicate intended here.
- Arbitrary affine opens U, U': `U V : S.affineOpens`, with the inclusion
  `hUV : U.1 ≤ V.1`. This subtype bundles exactly the affine-open hypothesis; it is
  not restricted to basic opens or a fixed affine cover.
- R and R' are `S.presheaf.obj (op U.1)` and `S.presheaf.obj (op V.1)`;
  A and A' in the node are `A.right.obj.obj (op U.1)` and `A.right.obj.obj (op V.1)`.
  Their restrictions are the corresponding functor maps of `(homOfLE hUV).op`.
- The specified structure morphism Spec A(U) → U is
  `Spec.map (A.hom.hom.app (op U.1)) ≫ U.2.isoSpec.inv`.
  `U.2.isoSpec` is the canonical identification U ≅ Spec O_S(U), not an arbitrary chart.
- Clause (i): `IsPushout σ_V res_O res_A σ_U` in `CommRingCat` expresses exactly
  that the canonical ring map A' ⊗_{R'} R → A is an isomorphism. Mathlib's
  `CommRingCat.isPushout_tensorProduct` identifies the pushout of σ_V and res_O
  with A' ⊗_{R'} R. The unique comparison to A has composites res_A and σ_U with
  the two tensor inclusions, so its pure-tensor formula is
  res_A(a') * σ_U(r) = r · a'|_U. Conversely, an isomorphism of this comparison
  makes the section square a pushout. Thus this formulation adds or removes no
  assertion. In particular it states the specified canonical map, not existence
  of some unspecified ring isomorphism. No extra scalar instances are assumed.
- Clause (ii), cartesianness and commutativity: `IsPullback` of the spectrum
  restriction, the two specified structure morphisms, and `S.homOfLE hUV`.
  `IsPullback` includes the square's commutativity and full universal property.
- Clause (ii), open immersion: `IsOpenImmersion (Spec.map res_A)`.
- Clause (ii), identification with the preimage: the explicit `Set.range` equation
  says its image is the inverse image of the image of `S.homOfLE hUV` under
  the structure map to V. Together with open immersion and the cartesian square,
  this gives the identification as schemes over U, not just a point-set claim.
- Clause (iii), triple: the second conjunct quantifies `U V W : S.affineOpens`
  and both inclusions, and equates the composite spectrum restrictions with the
  direct restriction for `hUV.trans hVW`.
- Clause (iii), identity: the last conjunct equates spectrum self-restriction
  with `𝟙 (Spec (A.right.obj.obj (op U.1)))` for every affine U.

Dependency declarations read and reused:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom` (schemes and their morphisms).
- `def-weil-sheaf-of-modules-category`: the node's Mathlib match `SheafOfModules`
  in `Mathlib.Algebra.Category.ModuleCat.Sheaf`; used through `A.toModule`.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.Coherent` was read in full;
  its quasi-coherent clause explicitly reuses `SheafOfModules.IsQuasicoherent`
  from `Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent`. No second
  quasi-coherence definition or coherent hypothesis is introduced.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`,
  `Mathlib.AlgebraicGeometry.Scheme`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, its projections,
  and universal property, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
  The actual square is stated as `IsPullback` (the universal property of that
  fibre product), not an arbitrarily chosen isomorphism to a fibre product.
- Added the already landed `def-weil-pbc-comm-algebra-sheaf` to `stmt_deps`;
  `Sheaf.AlgebraicGeometry.CommAlgebraSheaf`,
  `AlgebraicGeometry.Scheme.CommAlgebraSheaf` and `.toModule` were read in full.
  This is an existing definition node, so there are no new nodes or dependency modules.

Edge cases checked before writing: the empty scheme and empty affine opens are
included; their section rings may be zero rings and Mathlib's `CommRingCat`, Spec,
and pushout definitions allow this. Zero algebra sheaves are allowed. U = V and
U = V = W are included, with explicit identity and composition clauses. There is
no nonempty, Noetherian, separated, finite-type, or characteristic assumption.
All opens of an arbitrary `Scheme.{u}` are quantified, and all variables and the
universe are bound explicitly. No unbound implicit or `let` binder occurs.

Searches for an existing statement (all performed for this item):

- msearch `leanfinder`: “A quasi coherent sheaf of commutative algebras on a scheme
  restricts on nested affine opens by tensor base change, and the induced spectrum
  map is an open immersion”. Eight hits, chiefly structure-sheaf affine-chart
  lemmas; `PreservesLocalization.isOpenImmersion` assumes the affine-site
  coequifibered condition and gives only the immersion assertion, not this statement.
- msearch `loogle`: `AlgebraicGeometry.Scheme.Modules.IsQuasicoherent, Algebra.TensorProduct`.
  No hits (first identifier unknown); local source search found the actual
  `SheafOfModules.IsQuasicoherent` predicate.
- msearch `grep`: `SheafOfAlgebras|QuasicoherentAlgebra|PreservesLocalization`
  in Mathlib/AlgebraicGeometry. Six hits, the affine-site localization tools;
  no exact statement.
- msearch `leansearch`: “quasi coherent algebra sheaf affine open restriction tensor
  product cartesian spectrum”. Service unavailable: Internal Server Error.
  This supplies no mathematical search verdict.
- `rg` in the source `WeilConjectures` and project `lean/Sheaf` for algebra-sheaf,
  quasi-coherent algebra, and restriction names: found the shared CommAlgebraSheaf
  and QuasiCoherentAlgebra definitions and the relative-Spec theorem, but no
  exact nested-affine three-clause theorem. The latter was read: its chart clauses
  concern the glued relative spectrum, not the exact tensor restriction assertion.
- Source search for the item's blueprint id found no declaration.
- Mathlib `Ring/Constructions.lean` was read: `isPushout_tensorProduct` and
  `isPushout_iff_isPushout` verify the tensor meaning of the first clause.
- Searched Mathlib, the source and project modules for the new full declaration
  name: no match.

Validation: `scompile.py J1 lem-weil-pbc-quasi-coherent-algebra-affine-inclusion`
compiled the final module on the server in 2.0 seconds, with no errors or warnings.
The only deferred proof is the named theorem; its docstring includes all three
natural-language proof steps with the proof-dependency ids from the node.

## Second reading by J1

I read the unit statement in the copied node and the source statements of
Constructions Lemmas 01LN (tag 01LN) and 01LO (tag 01LO). The source situation
assumes a scheme `S`, a sheaf of commutative `O_S`-algebras `A` with
quasi-coherent underlying module, and nested affine opens. The Lean renders these
objects as `(S : Scheme.{u})`, `(A : S.CommAlgebraSheaf)`, and
`(hA : A.toModule.IsQuasicoherent)`, followed by affine-open subtypes `U V`
and `hUV : U.1 ≤ V.1`; no extra geometric, finiteness, characteristic, or
nonemptiness hypotheses occur.

The clauses match item by item. The node's section-ring tensor is rendered by
the exact pushout square
`IsPushout (A.hom.hom.app (op V.1)) (S.presheaf.map (homOfLE hUV).op)
(A.right.obj.map (homOfLE hUV).op) (A.hom.hom.app (op U.1))`; the imported
`CommRingCat.isPushout_tensorProduct` identifies this with the canonical map
`A(V) ⊗[O(V)] O(U) → A(U)`. The cartesian square is the following `IsPullback`,
using the canonical `isoSpec` charts and `S.homOfLE hUV`; the open-immersion
and image-preimage clauses are the following `IsOpenImmersion` and explicit
`Set.range` equality. The final two conjuncts quantify three nested affine opens
and one affine open respectively, and state composition and identity of the
contravariant spectrum restrictions in the same order as 01LO.

I checked dependency declarations: `Scheme`, `SheafOfModules.IsQuasicoherent`,
the coherent predicate's quasi-coherent clause, `Spec`/`Spec.map`, affine
pullbacks, and the landed `Scheme.CommAlgebraSheaf` encoding. No private copy
or second definition is used. Searches recorded in the worker report (source,
Mathlib, project `rg`, LeanFinder/Loogle, and LeanSearch) found no existing
statement; the LeanSearch service was unavailable but the other searches were
conclusive. The module's declaration name is fresh.

Edge cases are covered: arbitrary universe `u`, empty schemes and affine opens,
zero section rings and zero algebra sheaves, equal opens (`U = V`), and the
identity and triple-composition cases. The source imposes no Noetherian,
separated, finite-type, characteristic, or nonempty assumption, and neither
does Lean. All variables are explicitly bound and there are no `let` binders.

No mismatch was found, so no statement, dependency, or module change was
needed. The module was recompiled with `scompile.py`; it is clean apart from
the intentional theorem `sorry`. There is no statement correction and hence no
citer-holds review is required.
