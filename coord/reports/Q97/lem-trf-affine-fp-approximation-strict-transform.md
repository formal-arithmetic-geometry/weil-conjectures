## Worker report

The module `Sheaf.RingTheory.AffineFpApproximationStrictTransform` states
`Module.exists_affine_fp_approximation_strict_transform`, with one `sorry` proof.
It introduces no definitions, new nodes, dependency repairs, or statement corrections.
The current node has no Lean record. Its accepted stage-1 split is preserved verbatim;
coord/brief-stage2.md section 0 explicitly permits this stage-2 handoff despite the
inherited stage-1 unchanged-item BLOCKED ending. No released repair note exists.

Source read: literature/stacks-project/flat.tex, Tag 0810,
lemma-helper-blowup-affine-space, first proof paragraph. The accepted node abstracts
its finite-presentation replacement and power-torsion-quotient comparison to a ring
B, an element h, and arbitrary scalar extension D with a equal to the image of h
multiplied by c. The full six-step proof plan is in the theorem docstring.

Clause-by-clause correspondence:

- Commutative B and element h: `(B : Type u) [CommRing B] (h : B)`.
- The B-module N: `(N : Type v) [AddCommGroup N] [Module B N]`.
- Finite generation: `[Module.Finite B N]`.
- Finite presentation over B_h of N_h:
  `[Module.FinitePresentation (Localization (Submonoid.powers h))
  (LocalizedModule (Submonoid.powers h) N)]`.
- An integer n >= 0: `∃ n : ℕ`; no positivity restriction is imposed.
- Finite free source B^n and its surjection: `v : (Fin n → B) →ₗ[B] N`
  and `Function.Surjective v`. On the finite index set, the product module is
  canonically the direct sum in the node.
- Finite submodule K of ker v: `K : Submodule B (Fin n → B)`, `K.FG`, and
  `K ≤ LinearMap.ker v`.
- K_h = ker(v_h): `(K.localized (Submonoid.powers h)).restrictScalars B`
  equals the kernel of `IsLocalizedModule.map` between the canonical localization
  maps of the source and target. Restriction of scalars only lets the two existing
  APIs compare submodules of the identical localized ambient module: equality of
  underlying B-submodules is equivalent to equality of B_h-submodules.
- M is exactly B^n/K: every occurrence is `((Fin n → B) ⧸ K)`.
- Finite presentation of M: `Module.FinitePresentation B ((Fin n → B) ⧸ K)`.
- The induced surjection u: `∃ u : ((Fin n → B) ⧸ K) →ₗ[B] N`, with
  `u.comp K.mkQ = v` and `Function.Surjective u`. The equation characterizes the
  canonical induced map uniquely, because K.mkQ is surjective; this is not an
  arbitrary map or an additional mathematical hypothesis.
- u_h is an isomorphism: `Function.Bijective` of its canonical localized map.
  For a linear map, bijectivity is equivalent to being a linear isomorphism.
- Every commutative B-algebra D: `∀ (D : Type (max u v w)) [CommRing D]
  [Algebra B D]`; w is explicitly declared. The max convention accommodates all
  algebra sizes without a small-universe test-algebra restriction. Ring and module
  universes are independent.
- Elements a,c with a = h-bar c: `(a c : D), a = algebraMap B D h * c → ...`.
- The displayed canonical induced map is an isomorphism:
  `Function.Bijective (Submodule.torsion'QuotientMap (Submonoid.powers a)
  (LinearMap.baseChange D u))`. The source and target are exactly the quotients
  of `D ⊗[B] M` and `D ⊗[B] N` by their a-power torsion. By the actual definition
  `Submodule.powTorsion D Q a = Submodule.torsion' D Q (Submonoid.powers a)`,
  these are definitionally the recorded power-torsion submodules. This uses the
  existing induced map; no extra well-definedness helper or choice is needed.
  The dependency node's recorded scalar-extension convention puts D on the left;
  `TensorProduct.comm` identifies it with the node's M ⊗_B D and intertwines the
  induced maps, scalar actions, and torsion quotients.

Dependency declarations read and used:

- def-weil-finitely-generated-module: `Module.Finite`,
  Mathlib.RingTheory.Finiteness.Defs (publicly imported by FinitePresentation).
- def-sc-finitely-presented-module: `Module.FinitePresentation`,
  Mathlib.Algebra.Module.FinitePresentation.
- def-weil-pbc-module-localization: `LocalizedModule`,
  `LocalizedModule.mkLinearMap`, and `IsLocalizedModule.map`,
  Mathlib.Algebra.Module.LocalizedModule.Basic; `Submodule.localized` from
  Mathlib.Algebra.Module.LocalizedModule.Submodule gives the localized submodule.
  Both are publicly imported by the recorded torsion module. The actual canonical
  map API is `IsLocalizedModule.map`, as in the localization-exactness signature.
- def-weil-module-base-change: `LinearMap.baseChange`,
  Mathlib.LinearAlgebra.TensorProduct.Tower, using the dependency's recorded
  left-factor scalar-extension convention.
- def-nagata-power-torsion: `Submodule.powTorsion` and the existing
  `Submodule.torsion'QuotientMap`,
  WeilConjectures.Mathlib.Algebra.Module.Torsion. Full definition and map formula
  were read; the formula sends the class of x to the class of f(x).
- Proof dependency lem-weil-pbc-localization-module-exact:
  `LocalizedModule.map_exact`, Mathlib.Algebra.Module.LocalizedModule.Exact,
  imported privately for stage 3.
- Proof dependency lem-trf-finite-presentation-surjective-module-kernel:
  `Module.FinitePresentation.fg_ker`, Mathlib.Algebra.Module.FinitePresentation,
  already a public statement import. It assumes finite source, finitely presented
  target, and surjectivity, exactly the planned localized application.
- Proof dependency lem-weil-pbc-tensor-right-exact: `LinearMap.lTensor_exact`
  and `LinearMap.rTensor_exact`, Mathlib.LinearAlgebra.TensorProduct.RightExactness,
  imported privately for stage 3.

Edge cases checked before writing:

- n = 0 and N = 0 are permitted. Fin 0 → B is the zero module, and the
  empty kernel-generating list gives K = 0 where appropriate.
- h a unit: the conclusion forces an isomorphism already over B, consistently
  with N finitely presented under this hypothesis.
- h nilpotent (including h = 0): N_h is zero; localized-kernel equality is
  meaningful over the zero localization. K = 0 is allowed for the approximation.
- a = 0, or a nilpotent: power torsion is the entire module, so both quotient
  modules are zero. The isomorphism clause is still correct.
- c = 0 implies a = 0 and is allowed. The zero ring B or D is not excluded.
- Arbitrary nonflat D is included. Right exactness, followed by the finite-sum
  torsion-exponent argument, proves the kernel assertion without flatness.
- Exponent zero is allowed in the dependency's definition; it only kills zero.

Searches for an existing statement (2026-10-23):

1. msearch.py leansearch: "A finite module with finitely presented localization
   admits a finite presentation surjecting onto it with identical localization
   and power torsion quotients after scalar extension". Eight hits, including
   Module.FinitePresentation.exists_lift_of_isLocalizedModule and
   IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation.
   Neither constructs this approximation or compares power-torsion quotients.
2. msearch.py leanfinder: "A finite module finitely presented after inverting h
   admits a finitely presented surjection that is an isomorphism after localization
   and on base change modulo power torsion". Eight hits, including
   exists_bijective_map_powers, exists_notMem_bijective, and localized-module
   lifting theorems. They start with an existing map or finitely presented modules;
   no exact match.
3. msearch.py loogle: "Module.FinitePresentation, LocalizedModule". Twelve hits
   describing localization of finitely presented modules, localization of Hom,
   and spreading existing maps. No approximation-plus-torsion comparison.
4. msearch.py grep, RingTheory:
   "powTorsion|finitePresentation.*local|exists.*[Ff]inite[Pp]resentation".
   Twenty-five hits on local finite presentation, free localization, and flat
   factorization; no matching statement.
5. rg over lean/WeilConjectures and lean/Sheaf for the item id,
   fpApproximation, approximation.*[Tt]orsion, [Tt]orsion.*[Aa]pproximation;
   only unrelated generic-sheaf approximation results. A focused check of the
   RingTheory source and existing torsion-quotient module found the reusable
   canonical map and its elementary properties, not this theorem. The prospective
   declaration name does not occur in either source tree.

Validation: scompile.py compiled both its sandbox probe and the actual module
against the published server library in about 2 seconds each, without errors or
unexpected warnings. All universes and term variables are bound explicitly.
No STATEMENT-DISPUTED issue was found.

## Second reading by Q97

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
