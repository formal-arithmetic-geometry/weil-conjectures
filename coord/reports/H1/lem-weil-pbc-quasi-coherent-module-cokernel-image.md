## Worker report

The module lean/Sheaf/AlgebraicGeometry/Modules/QuasiCoherentCokernelImage.lean states
AlgebraicGeometry.Scheme.Modules.quasiCoherent_cokernel_image, with one sorry and no
new definitions or auxiliary theorems. The node copy changes only lean.

Source read: [Stacks 01IC](https://stacks.math.columbia.edu/tag/01IC),
[01LB](https://stacks.math.columbia.edu/tag/01LB), and
[01AH](https://stacks.math.columbia.edu/tag/01AH). The local Stacks checkout is absent
on this machine, so these official pages were opened. They confirm affine kernel/cokernel
closure, global closure, and colimits as sheafified presheaf colimits, respectively.

Hypotheses and objects:
- X is an arbitrary scheme: `{X : Scheme.{u}}`.
- F and G are O_X-modules and φ is an O_X-linear sheaf morphism:
  `{F G : X.Modules} (φ : F ⟶ G)`.
- Both are quasi-coherent: `[F.IsQuasicoherent] [G.IsQuasicoherent]`.
- Coker φ and q are `cokernel φ` and `cokernel.π φ`. This uses the existing
  categorical cokernel, rather than constructing a second quotient sheaf. Mathlib's
  SheafOfModules colimit instance is obtained from PresheafOfModules.sheafification
  and its adjunction. Hence this object is the sheafified presheaf quotient described
  in the node, with its canonical projection, up to the unique compatible isomorphism
  implicit in the node's phrase "the cokernel". It does not assert sectionwise
  surjectivity on arbitrary opens.
- Im φ is `Abelian.image φ`, definitionally `kernel (cokernel.π φ)`;
  its inclusion is `Abelian.image.ι φ`. Its agreement with the node's local-image
  description is an explicit conclusion, not a hypothesis or a new private definition.

Clause (1):
- The image is a sub-O_X-module: `Mono (Abelian.image.ι φ)`; its object and inclusion
  already belong to the O_X-module category. The sectionwise submodule is
  `LinearMap.range ((Abelian.image.ι φ).val.app (op W)).hom`.
- It equals the sectionwise kernel of q: for every open W this range equals
  `LinearMap.ker ((cokernel.π φ).val.app (op W)).hom`.
- For every W and section s, membership in the inclusion's range is equivalent to
  `∀ x : X, x ∈ W → ∃ (V : X.Opens) (h : V ≤ W), x ∈ V ∧ ∃ t : Γ(F, V),
  φ.app V t = G.presheaf.map (homOfLE h).op s`. Thus the image is exactly the
  subsheaf of sections locally in the image, using arbitrary open neighbourhoods.
- Factorization: `Abelian.factorThruImage φ ≫ Abelian.image.ι φ = φ`.
- q is an epimorphism: `Epi (cokernel.π φ)`.
- q composed with φ is zero: `φ ≫ cokernel.π φ = 0` (Lean composes left to right).

Clause (2): `(cokernel φ).IsQuasicoherent ∧ (Abelian.image φ).IsQuasicoherent`.

Clause (3), quantified over every `U : X.affineOpens`:
- Im φ(U) = φ_U(F(U)): equality of the two `Set.range`s in Γ(G,U).
- Surjectivity of q_U: `Function.Surjective ((cokernel.π φ).app U.1)`.
- Its kernel is the image: equality of the corresponding `LinearMap.ker` and
  `LinearMap.range` over Γ(X,U).
- The quotient-module identification is `∃ e : (Γ(G,U) ⧸ range φ_U) ≃ₗ[Γ(X,U)]
  Γ(cokernel φ,U)`, and the following `∀ s` equation says e sends the quotient
  class of s to q_U(s). This states the canonical quotient identification, including
  its compatibility with q, rather than an unrelated abstract module isomorphism.

Dependency declarations read and used:
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, AlgebraicGeometry.Scheme (and Hom).
- def-weil-sheaf-of-modules-category: Mathlib.Algebra.Category.ModuleCat.Sheaf,
  SheafOfModules and Hom; specialized by Mathlib.AlgebraicGeometry.Modules.Sheaf,
  AlgebraicGeometry.Scheme.Modules, its category/abelian/colimit instances and Hom.app.
- pqf-def-coherent: imported Sheaf.AlgebraicGeometry.Coherent; as its module docstring
  explicitly specifies, the quasi-coherent clause is Mathlib's
  SheafOfModules.IsQuasicoherent, whose signature/docstring were read in
  Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent. Its IsCoherent definition
  is not needed because the item assumes only quasi-coherence.
- def-weil-pbc-sheafification: CategoryTheory.presheafToSheaf and
  CategoryTheory.sheafificationAdjunction in Mathlib.CategoryTheory.Sites.Sheafification.
  The module-specific implementation is PresheafOfModules.sheafification and
  PresheafOfModules.sheafificationAdjunction, already used by the module category's
  colimit and abelian instances; no replacement definition is introduced.
- Image: Mathlib.CategoryTheory.Abelian.Images, Abelian.image, image.ι,
  factorThruImage; the full abbreviations were read.

Edge cases checked mathematically before writing: empty scheme and empty open
(the local criterion is vacuous and the sheaf of modules has only the zero section),
zero source (zero image and target cokernel), zero target (both zero), zero morphism
(zero image and target cokernel), and identity morphism (full image and zero cokernel).
There is no nonempty, finiteness, Noetherian, separatedness or field hypothesis.
One universe u matches X.Modules' established carrier; arbitrary affine opens are
included without imposing a presentation or chosen coordinate ring.

Searches actually run:
- msearch.py leanfinder: "cokernel and image of quasi coherent modules are quasi
  coherent and sections on affine opens are module quotient". Eight hits, all
  generatorsOfIsCokernelFree / relationsOfIsCokernelFree / presentationOfIsCokernelFree;
  these concern free presentations, not this closure and affine-sections statement.
- msearch.py loogle: "SheafOfModules.IsQuasicoherent, CategoryTheory.Limits.cokernel".
  Zero hits.
- msearch.py grep: "isQuasicoherent_cokernel|isQuasicoherent_image|cokernelIsoRangeQuotient".
  Six hits, all ModuleCat.cokernelIsoRangeQuotient or its uses, for modules over one
  ring, not quasi-coherent sheaves on arbitrary schemes.
- msearch.py leansearch: "cokernel image quasi coherent sheaf affine sections quotient".
  Service unavailable (Internal Server Error); no negative mathematical conclusion
  is drawn from this failure.
- rg on WeilConjectures and lean/Sheaf for IsQuasicoherent, cokernel, image and quasi:
  related material (QuasicoherentKernel, coherent closure, ideal/module products)
  but no exact statement. Searching the item's literal id in WeilConjectures returned
  no occurrence. tools/lean_names_upstream.py show for the item gave no attachment.
- rg across Mathlib, WeilConjectures and lean/Sheaf for
  "quasiCoherent_cokernel_image|isQuasicoherent_cokernel|isQuasicoherent_image": no hits;
  the new full declaration name does not collide with any existing declaration.

Validation: scompile.py on this module returned exit code 0, compiled in 3.1 seconds,
with no warnings. No statement fault or dispute was found, and no correction is made.


## Second reading by H1

I reread the node statement and the Lean signature item by item. The introduced scheme is
`{X : Scheme.{u}}`; Lean uses exactly this arbitrary scheme carrier. The morphism is
`(φ : F ⟶ G)` with `{F G : X.Modules}`, and the two quasi-coherence hypotheses are
`[F.IsQuasicoherent] [G.IsQuasicoherent]`, with no Noetherian, separated, finiteness,
field, or nonemptiness assumptions. The node's cokernel `q` is rendered by
`cokernel φ` and `cokernel.π φ`, and the image by `Abelian.image φ` and
`Abelian.image.ι φ`; these are the existing categorical notions in the stated module
category, rather than private definitions.

Clause (1) is rendered by `Mono (Abelian.image.ι φ)`, the all-open equality of
`LinearMap.range ((Abelian.image.ι φ).val.app (op W)).hom` with the corresponding
`LinearMap.ker`, and the following local-section equivalence over every point of every
open. The factorization, epimorphism, and zero-composite clauses are respectively
`Abelian.factorThruImage φ ≫ Abelian.image.ι φ = φ`, `Epi (cokernel.π φ)`, and
`φ ≫ cokernel.π φ = 0`. Clause (2) is exactly the conjunction
`(cokernel φ).IsQuasicoherent ∧ (Abelian.image φ).IsQuasicoherent`. Clause (3)
quantifies over every `U : X.affineOpens` and gives the image/range equality,
surjectivity of the affine cokernel map, kernel/range equality, and the explicit linear
equivalence from the quotient module sending each quotient class to its cokernel image.
The quantifier order and all four affine conclusions agree with the node.

I checked edge cases: empty schemes and opens, zero source or target, zero and identity
morphisms, and the vacuous local condition. The universe is tied to the scheme and no
case is excluded. Searches in Mathlib, `WeilConjectures`, and `lean/Sheaf`, together
with LeanFinder/Loogle/LeanSearch searches recorded in the worker report, found no
existing declaration of this statement or notion; the related ring-module quotient
lemmas are not substitutes.

No mismatch was found, so no source or node correction was needed. I reran
`scompile.py`; the module compiled cleanly with only its permitted `sorry` proof.
