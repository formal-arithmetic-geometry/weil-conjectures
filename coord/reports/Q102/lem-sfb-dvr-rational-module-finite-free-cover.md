## Worker report

The module Sheaf.RepresentationTheory.DvrRationalModuleFiniteFreeCover states
AlgebraicGeometry.exists_finite_basis_equivariant_surjection_of_dvr with one sorry.
It constructs no definitions and leaves the natural-language node and dependency lists unchanged.
No new node or dependency repair is needed: the coactions are expressed by linear maps and
explicit equations, rather than a second private definition of rational module.

Source checked: [Alper, printed p.521](https://content.algebraicgeometry.nl/2014-4/2014-4-022.pdf),
Definition 9.2.2, Remark 9.2.3 and Remark 9.2.4(i). The resolution property there supplies
finite rank equivariant locally free covers; its affine form supplies finite free covers.
A DVR has the required regular Noetherian separated base of dimension one.
Affineness of the group morphism implies separatedness, so no separate assumption is needed.
The statement agrees with this source. No STATEMENT-DISPUTED issue was found.

Clause-by-clause correspondence:

- The DVR is `A : CommRingCat.{u}` with `[IsDomain A] [IsDiscreteValuationRing A]`.
  Bundling the ring exposes exactly the base used by Mathlib's coordinate Hopf construction;
  every commutative ring can be supplied as `CommRingCat.of A`.
- The scheme `H : Scheme.{u}` with `[H.Over (Spec A)]` has its given structure morphism.
  `[GrpObj (H.asOver (Spec A))]` supplies the actual group-object diagrams over the base.
- `[IsAffine H]` expresses that H is affine. Since Spec A is affine, this is equivalent
  to the node's affine structure morphism (`isAffine_of_isAffineHom` and
  `isAffineHom_of_isAffine`). `[Flat (H ↘ Spec A)]` is exactly flatness.
- `[LocallyOfFinitePresentation (H ↘ Spec A)]` supplies finite presentation locally.
  An affine morphism is quasi-compact and separated, hence quasi-separated, so together
  these are exactly finite presentation; there is no missing quasi-compactness condition.
- `Γ(H, ⊤)` is C = A[H]. Mathlib.AlgebraicGeometry.Group.Affine supplies its canonical
  A-algebra, bialgebra and Hopf algebra from these very diagrams. `Coalgebra.comul` and
  `Coalgebra.counit` are their comultiplication and counit, not arbitrary extra parameters.
- `N : Type v`, `[AddCommGroup N] [Module A N]` gives the underlying A-module;
  `[Module.Finite A N]` means the top submodule is spanned by a finite subset, exactly the
  node's finite-generation condition. The independent universe v permits large carriers.
- `ρN : N →ₗ[A] N ⊗[A] Γ(H, ⊤)` is the specified linear coaction.
  `hcoassoc` identifies `(rho_N tensor 1) rho_N`, after the canonical tensor associator,
  with `(1 tensor Delta) rho_N`. `hcounit` identifies `(1 tensor epsilon) rho_N` with
  the identity after the canonical right unitor. Thus both rational-module axioms occur.
- `∃ (P : ModuleCat.{u} A) (n : ℕ) (_ : Module.Basis (Fin n) A P)` gives an A-module
  with a finite basis, including an empty basis. Using a bundled module merely binds its
  additive group and scalar structure. The universe u imposes no mathematical restriction:
  every finite free A-module has an A^n model in this universe; an arbitrary finite basis
  can be reindexed by Fin n and transported to this model.
- `ρP` is an A-linear coaction on P; the first two conjuncts are exactly its coassociativity
  and counit equations, with the same canonical coordinate coalgebra as for N.
- `p : P →ₗ[A] N` is the desired A-linear map. `Function.Surjective p` supplies the
  required surjection and the final conjunct is `(p tensor 1_C) rho_P = rho_N p`.
- No torsion-freeness of N, smoothness, connectedness or reductivity of H is assumed.
  There is no positivity constraint on n and no nonzero constraint on N.

Dependency declarations read and used:

- def-sc-discrete-valuation-ring: `IsDiscreteValuationRing`,
  Mathlib.RingTheory.DiscreteValuationRing.Basic (local PID domain, not a field).
- def-sc-group-scheme: `CategoryTheory.GrpObj`, Mathlib.CategoryTheory.Monoidal.Grp,
  used over Spec A. The general group-object declaration is valid over arbitrary rings;
  the field specialization in its node does not restrict the declaration. Its full group
  scheme convention is also documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- def-weil-flat-morphism: `AlgebraicGeometry.Flat`,
  Mathlib.AlgebraicGeometry.Morphisms.Flat (equivalent to stalkwise flatness).
- pqf-def-affine-morphism: `AlgebraicGeometry.IsAffineHom`,
  Mathlib.AlgebraicGeometry.Morphisms.Affine; source affineness over affine Spec A is the
  equivalent form used to access the coordinate Hopf instance.
- def-sbc-locally-finite-presentation: `AlgebraicGeometry.LocallyOfFinitePresentation`,
  Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec`, Mathlib.AlgebraicGeometry.Scheme.
- def-weil-pbc-module-tensor-product: `TensorProduct`,
  Mathlib.LinearAlgebra.TensorProduct.Defs; `LinearMap.rTensor` and `LinearMap.lTensor`
  in Mathlib.LinearAlgebra.TensorProduct.Map render all tensor maps.
  `TensorProduct.assoc` and `TensorProduct.rid` in the Associator module render the
  canonical identifications suppressed in the node's equations.

Proof dependency imports are Mathlib.RingTheory.Flat.Basic (`Module.Flat.rTensor_exact`,
`Module.Flat.lTensor_exact`), Mathlib.RingTheory.RingHom.Flat (`RingHom.Flat`), and the
public modules for the DVR, tensor product and affine flatness criterion (`flat_iff`).
The proof-only nodes lem-sfb-dvr-comodule-finite-free-lattice and
lem-sfb-flat-coalgebra-subcomodule-core currently have neither a Lean record nor a Mathlib
match; they supply no object needed to type this statement, so there is no module to import.
Their proof uses are retained in the theorem docstring, which includes all six node steps.

Edge cases checked mathematically before writing: N = 0 allows P = 0, n = 0, and the unique
coaction and surjection. For N = A/(t), the trivial group permits the ordinary rank-one
quotient A -> A/(t), showing that no torsion-free hypothesis slipped in. For the trivial
group, C = A and the counit equation gives the usual trivial rational action, reducing to
ordinary finite free covers. Finite non-smooth group schemes and every residue
characteristic remain allowed. No field case was added to the DVR definition.

Searches for an existing theorem:

- msearch.py leanfinder: "finite rational modules for flat affine group scheme over
  discrete valuation ring admit finite free equivariant surjections" returned eight
  ordinary module flatness/finiteness facts, including Module.Finite.exists_free_surjective;
  none includes a rational coaction and its equivariance square.
- msearch.py loogle: `"Comodule", "Free"` returned zero hits.
- msearch.py leansearch: "A finite comodule over a flat Hopf algebra over a discrete
  valuation ring is a quotient of a finite free comodule" returned ordinary finite-module
  presentations and local flat/free facts; none is the requested equivariant theorem.
- msearch.py grep: `resolutionProperty|resolution_property|equivariant.*surject|surject.*equivariant`
  found only a GroupAction multiple-transitivity result, not this statement.
- rg in WeilConjectures and Sheaf for coaction, Comodule, rational module, coordinate
  Hopf, resolution property, finite free covers and the proposed declaration name found
  no exact cover theorem. The exact node-id search in WeilConjectures had zero hits.
  The existing HopfAction coaction wrappers are field-specific, and the relative Hopf
  module structures have extra action data; neither is copied or used to restrict A.
- rg in Mathlib's Group/Affine found the canonical HopfAlgebra instance on global sections
  of an affine group scheme over any bundled commutative ring. Its full source and the
  coalgebra and tensor-map signatures were read before writing the statement.
  The proposed full declaration name is absent from dag/lean_names_upstream.json.

Validation: scompile.py Q102 lem-sfb-dvr-rational-module-finite-free-cover compiled the
single module in both sandbox and library modes, exit 0, in 2.9 and 2.8 seconds respectively;
no warnings were printed. `set_option autoImplicit false` enforces explicit variable binding.
The only postponed proof is the named theorem matching this node.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
