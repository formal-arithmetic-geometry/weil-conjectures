## Worker report

The module `Sheaf.TraceFormula.LocalHomotopyUnitDeterminantLift` states
`LinearMap.exists_local_homotopy_unit_determinant_lift`, with its entire proof
`sorry`. No definition, helper theorem, dependency repair, or new node is needed.
The sole node change is its `lean` record.

Read the complete item and its six proof steps, all three statement-dependency
nodes and their recorded Mathlib declarations, and all proof-dependency records.
Read Stacks `more-algebra.tex` at `lemma-homotopic-surjections` (Tag 0FJK),
lines 37016–37120, and `lemma-det-switch` (Tag 0FJF), lines 36420–36458.
The source's argument for degree-zero surjectivity uses its surrounding
quasi-isomorphism assumption; this node instead supplies the valid explicit
inverse `1 - dP w t`. It therefore needs no additional quasi-isomorphism
hypothesis and no statement correction.

Hypotheses and clauses, in statement order:

- Commutative local ring: `{R : Type u} [CommRing R] [IsLocalRing R]`.
- The four finite free terms: `P₁`, `P₀`, `Q₁`, `Q₀`, each with
  `AddCommGroup`, `Module R`, `Module.Free R`, and `Module.Finite R`.
  Their four universes are independent of one another and of the ring universe.
- The complexes `[P₁ → P₀]` and `[Q₁ → Q₀]` are displayed directly by
  `dP : P₁ →ₗ[R] P₀` and `dQ : Q₁ →ₗ[R] Q₀`. These are precisely the
  data of two-term complexes zero outside degrees -1 and 0: there is no
  additional differential-composition condition. This presentation uses the
  original modules, without replacing them by tuple modules or derived objects.
- The morphisms are displayed by `a₁`, `a₀`, `b₁`, `b₀`; `ha` and `hb`
  are exactly their chain-map equations. `ha₁`, `hb₁`, `ha₀`, `hb₀` are
  the four surjectivity hypotheses. None is omitted even though some are
  unnecessary to the construction.
- The linear homotopy is `h : P₀ →ₗ[R] Q₁`, with `hh₀` and `hh₁` the
  two prescribed difference equations, with the sign `b - a`.
- The common submodule is `U : Submodule R P₁`. The equivalences
  `eA eB : U ≃ₗ[R] Q₁` have underlying maps exactly `a₁.domRestrict U`
  and `b₁.domRestrict U`. `IsCompl (LinearMap.ker a₁) U` expresses
  the direct-sum decomposition used by the block clause.
- `s = U.subtype.comp eA.symm.toLinearMap` is the specified section, not
  an arbitrary right inverse. `t = s.comp h` and `a₁.comp t = h` fix
  the lift and its stated property.
- `K : P₁ ≃ₗ[R] P₁` and `L : P₀ ≃ₗ[R] P₀` are the negative and zero
  components of the chain automorphism, with underlying maps `id + t dP`
  and `id + dP t`. The commutation equation `dP K = L dP` gives the
  chain automorphism. Both equations `a₁ K = b₁` and `a₀ L = b₀` give
  `ak = b` in every nonzero degree.
- `C : ker a₁ →ₗ[R] U` has inclusion exactly `tdP` restricted to the
  kernel. For arbitrary `n : ker a₁` and `x : U`, the forward equation
  is `K(n+x) = n + (Cn + eA.symm (eB x))`. Thus the upper blocks are
  `(1,0)` and the lower blocks are `(C,B)` with `B = eA⁻¹ eB`.
- The inverse block equation is
  `K.symm(n+x) = n + eB.symm (eA (x-Cn))`. This is exactly
  `(1,0;-B⁻¹C,B⁻¹)` by linearity. No freeness hypothesis on the kernel
  is introduced.
- `L.symm.toLinearMap = id - dP.comp (K.symm.toLinearMap.comp t)` is
  the stated zero-degree inverse. Its chain-map equation is also explicit;
  this just expresses the inverse being a chain map.
- For every pair of finite bases `c₁ : Basis (Fin r₁) R P₁` and
  `c₀ : Basis (Fin r₀) R P₀`, the matrix determinants of `L` and `K`
  are equal. This allows every finite rank and every finite basis, with
  finite index sets reindexed by `Fin`; no chosen basis is fixed as a
  hypothesis of the theorem.
- The final equality uses `TensorProduct.map` on
  `exteriorPower.map (Module.finrank R P₀) L.toLinearMap` and
  `(exteriorPower.map (Module.finrank R P₁) K.symm.toLinearMap).dualMap`.
  It is an equality with `LinearMap.id` on the actual module
  `⋀[R]^(Module.finrank R P₀) P₀ ⊗[R]
    Module.Dual R (⋀[R]^(Module.finrank R P₁) P₁)`.
  Thus the positive factor is first, and the negative factor is inverse
  before dualization, exactly as in the node. This is not merely an
  equality of scalar determinants.

Statement-dependency declarations used:

- `Mathlib.LinearAlgebra.FreeModule.Basic`: `Module.Free`; finite generation
  is Mathlib's `Module.Finite`, giving exactly finite free modules together.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the recorded framework
  `DerivedCategory`/`HasDerivedCategory` is publicly imported. Here only its
  underlying notion of complex and chain map is needed, displayed in the
  two nonzero degrees, rather than passing to a derived category.
- `Mathlib.LinearAlgebra.ExteriorAlgebra.Basic`: `ExteriorAlgebra` and
  `exteriorPower`; `Mathlib.LinearAlgebra.ExteriorPower.Basic` supplies
  `exteriorPower.map` on these same exterior powers.

Other standard APIs: `LinearMap.domRestrict`, `LinearMap.ker`, `LinearEquiv`,
`Module.finrank`, `LinearMap.toMatrix`, `Matrix.det`, `LinearMap.dualMap`,
`TensorProduct.map`, and `IsCompl`. Proof imports are the recorded
`Sheaf.TraceFormula.LocalCommonSummandSurjections` declaration
`exists_common_summand_surjections`, `Mathlib.LinearAlgebra.Matrix.SchurComplement`
for `Matrix.det_one_add_mul_comm`, and
`Mathlib.LinearAlgebra.ExteriorPower.Basis` for `Module.Basis.exteriorPower`
and `exteriorPower.coe_basis` (the remaining zero/one exterior equivalences
are in ExteriorPower.Basic). Their signatures and docstrings were read.

Edge cases checked mathematically: either P rank may be zero (the basis
quantifiers allow `Fin 0`, and top exterior degree zero is R); Q terms
may also be zero. If `h=0`, take both components to be identity and C=0.
If `dP=0`, both components are identity, and the homotopy equations force
`a=b` in degree -1 and make the zero-degree equation compatible through
`a` being a chain map. Residue field F₂ requires no division or sign
assumption; the block inverse and determinant switch remain valid.
There is no quasi-isomorphism assumption and no restriction on the
relation between the two ranks. `IsLocalRing` uses the usual nonzero
local-ring convention (exactly one maximal ideal excludes the zero ring).

Searches actually run with `msearch.py Q54 <item>`:

- LeanFinder: `Homotopic surjective maps of finite free two term complexes
  over a local ring factor through a chain automorphism acting trivially
  on the determinant line`. Eight hits, headed by
  `ComplexShape.QFactorsThroughHomotopy`; these concern homotopy-category
  localization and do not give this automorphism or its determinant action.
- Loogle: `LinearMap.det, Homotopy`. Zero hits.
- grep in Mathlib LinearAlgebra: `homotop.*surject|det_one_add|one_add.*comp`.
  Ten hits; `Matrix.det_one_add_mul_comm` gives only the already recorded
  determinant-switch proof dependency, not the present statement.
- LeanSearch: `A local homotopy between degreewise surjections of finite
  free two term complexes lifts to a chain automorphism with equal
  determinants in both degrees`. Eight hits, headed by
  `CategoryTheory.ProjectiveResolution.liftHomotopy`; no exact match.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for homotopy/surjection/determinant wording,
  the proposed declaration name, and this blueprint id: no declaration
  of this statement. The project search finds the common-summand proof
  dependency and sheaf determinant constructions, which do not state this
  local algebraic lift. The exact blueprint id has no upstream match.
- Read the existing project determinant modules
  `AffineTwoTermDeterminant.lean`, `CanonicalTwoTermPerfectDeterminant.lean`
  and upstream `LinearAlgebra/ExteriorPower/Top.lean` to check that no
  equivalent local homotopy-lift statement was being duplicated.

Validation: `scompile.py Q54 lem-trf-local-homotopy-unit-determinant-lift
<module file>` succeeded in sandbox and library mode with no errors or
warnings. No statement dispute or node fault remains.

## Second reading by Q54

This is the author's fresh second reading; the dispatcher's explicit
single-worker instruction forbids spawning an independent reader. The
maintainer supplies independent review after delivery.

Reopened the complete node and the module together and checked the four
finite-free assumptions, both chain-map equations, all four surjectivity
hypotheses, and both homotopy signs. The statement retains each one.
Checked that the two-term display has precisely the source's nonzero
modules and differential, rather than requiring an extra exactness or
quasi-isomorphism assumption. The common summand is for both restrictions,
and the section is specifically the inverse of the a-restriction.

Checked every conclusion against the Lean in order: section/lift, both
component formulas and their invertibility, chain commutation, both `ak=b`
equations, C's restriction formula, the forward blocks, the inverse blocks,
the zero-degree inverse, its chain commutation, determinant equality for
all bases, and the identity of the positive-first exterior/dual tensor map.
In particular `eB.symm (eA (x-Cn))` has the correct order B⁻¹, and
`K.symm` occurs before dualization in the final clause. The finite basis
quantifiers permit rank zero, and the four module universes are explicitly
independent. No mismatch or change was found in this rereading. No new
node, dependency module, or statement correction is involved.
