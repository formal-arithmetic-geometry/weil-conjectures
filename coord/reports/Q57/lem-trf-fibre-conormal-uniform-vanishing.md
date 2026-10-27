## Worker report

Item: lem-trf-fibre-conormal-uniform-vanishing. The new module
`Sheaf.AlgebraicGeometry.FibreConormalUniformVanishing` states
`AlgebraicGeometry.Scheme.Modules.fibre_conormal_uniform_vanishing`, with its sole
proof `sorry`. It introduces no definitions. The source was read in
`literature/stacks-project/coherent.tex`, Tag 0D2M, especially lines 6013–6044:
the graded-module argument with F = O_X. All other node fields are unchanged.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| A is a commutative ring | `(A : Type u) [CommRing A]` |
| A is Noetherian | `[IsNoetherianRing A]` |
| A has a unique maximal ideal m | `[IsLocalRing A]`, with `IsLocalRing.maximalIdeal A` as m. Mathlib's `maximal_ideal_unique` and `of_unique_max_ideal` identify this with the node's hypothesis. The zero ring is excluded already by existence of a maximal ideal. |
| k = A/m | `A ⧸ IsLocalRing.maximalIdeal A`, the codomain of `Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)` |
| g : X -> Spec A is proper | `{X : Scheme.{u}} (g : X ⟶ Spec (.of A)) [IsProper g]` |
| X_0 = X times_(Spec A) Spec k | `Limits.pullback g (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))` |
| i : X_0 -> X | `Limits.pullback.fst g` applied to that exact residue spectrum map |
| J = m O_X, the extended ideal | `((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))).ker.comap g)`. The quotient spectrum map has ideal m-tilde; `comap` is precisely the kernel of the projection from its closed-subscheme base change, as in def-nagata-extended-ideal. No arbitrary ideal is assumed. |
| N is an invertible O_X-module | `(N : X.Modules) [N.IsInvertible]` |
| i^*N is ample | `hN : @IsAmple X_0 ((tensorPullback i).obj N) ((invertible_pullback_tensor i).1 N).2`. The displayed i and X_0 are fully expanded in the file. The invertibility witness is supplied by the recorded theorem, not by an added hypothesis. |
| J^0 = O_X and the prescribed ideal powers | `(Scheme.idealSheafPower J.toModulesι n).1`; at zero the definition is the structure module, at one it is J, and at successors it is the ideal-module image product. |
| J^n/J^(n+1) | `formalModuleQuotient J 1 (Scheme.idealSheafPower J.toModulesι n).1`. The formal quotient is the cokernel of the product inclusion, so this is J^n/(J J^n). For n >= 1 its denominator is the recursive J^(n+1). At n = 0, the image of J tensor O_X -> O_X is J, so it is O_X/J. |
| tensor with N^(tensor d) | `... ⊗ N.tensorPow d` in the existing monoidal category of scheme modules; tensorPow zero is O_X |
| H^1(X, ...) = 0 | `IsZero ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj (...))`. This is an actual ModuleCat object, not `IsZero` on a bare type. The functor is the right derived functor of module-valued global sections. |
| exists an integer d_0 >= 0 | `∃ d₀ : ℕ` |
| simultaneously for every n >= 0, d >= d_0 | `∀ n d : ℕ, d₀ ≤ d → ...`, after the existential. Natural indices are exactly the nonnegative integer indices, and d >= d_0 >= 0 excludes no integer in the source statement. The bound cannot depend on n. |

### Dependency declarations used

Read the statements and lean/mathlib records of all thirteen statement dependencies,
and opened the relevant declaration signatures and docstrings in the live source clone.
The import list includes the recorded statement modules as public imports and the
available proof-dependency modules as ordinary imports (except where a proof witness
occurs in the statement, which requires public visibility).

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (all ideals finitely generated).
- `def-weil-proper-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Proper`,
  `AlgebraicGeometry.IsProper`; universally closed implies quasi-compact, so the
  locally-finite-type formulation agrees with properness in the node.
- `def-pc-scheme` and `def-weil-affine-spectrum`:
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`.
- `def-pc-fibre-product`:
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `CategoryTheory.Limits.pullback` and `pullback.fst`.
- `def-pc-scheme-fibre`: `Mathlib.AlgebraicGeometry.Fiber`,
  `Scheme.Hom.fiber`, `fiberι`, `fiberToSpecResidueField`. That general fibre uses
  the residue field of a point. Here the node fixes k literally as A/m, so the
  displayed pullback along the quotient map is used directly, rather than a second
  fibre definition or an implicit identification with a differently presented field.
- `def-nagata-extended-ideal`: `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`,
  `Scheme.IdealSheafData.comap`; the input ideal is the kernel of the residue
  quotient spectrum map, `Scheme.Hom.ker` from IdealSheaf.Basic.
- `def-sc-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Modules.Invertible`,
  `Scheme.Modules.IsInvertible`, the scheme-module monoidal tensor and `tensorPow`.
- `def-pc-module-pullback`:
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`, retaining the upstream
  `Scheme.Modules.tensorPullback` with its actual inverse-image and extension-of-scalars
  construction. No use of Mathlib's differently recorded module pullback in the signature.
- `def-weil-pbc-ample-invertible-module`:
  `WeilConjectures.AlgebraicGeometry.Ample`, `Scheme.Modules.IsAmple` and the
  above `tensorPow`. Its explicit invertibility proof is supplied by
  `WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor`,
  `Scheme.Modules.invertible_pullback_tensor`, already a proof dependency of the item.
- `def-weil-pbc-coherent-formal-module`:
  `WeilConjectures.AlgebraicGeometry.CoherentFormalModule`, `formalModuleQuotient`,
  using the publicly imported `Scheme.idealSheafPower` and `idealModuleProductι`
  from `WeilConjectures.AlgebraicGeometry.IdealModuleProductStalk`.
- `def-pur-sheaf-tensor-product`:
  `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`,
  `SheafOfModules.cochainModulesMonoidal`, retaining the shared localization tensor.
  The scheme tensor and tensor powers use that same sheaf tensor construction.
- `pqf-def-cohomology`: `WeilConjectures.AlgebraicGeometry.PQFCohomology`,
  `sheafCohomologyAndHigherDirectImages`, and its public
  `RingedSpace.moduleCohomology` from
  `WeilConjectures.Topology.RingedSpaceModuleCohomology`.

### Edge cases

Checked mathematically before writing the statement:

- n = 0: the numerator is O_X, giving the essential layer O_X/J, not a zero layer.
- d = 0: included if the chosen bound is zero; tensorPow zero is the monoidal unit.
  The statement does not claim that zero is always a permissible bound.
- A a field: m = 0, so positive layers vanish; the n = 0 clause is ordinary H^1
  Serre vanishing. No nonzero maximal ideal assumption is present.
- Nilpotent maximal ideal: sufficiently high layers vanish; no domain, reducedness,
  or regularity assumption has been added.
- Nonflat X over A: ideal powers are image products, not tensor powers, and no
  flatness assumption is present.
- Empty X: no Nonempty X assumption. All cohomology groups vanish and d_0 = 0 works.
- A with no maximal ideal (the zero ring): the node requires a unique maximal ideal,
  so this is correctly excluded by IsLocalRing's Nontrivial component.
- The source allows any scheme size and any ring size within a common sufficiently
  large universe; `u` is explicit, with no auto-bound variable or universe.

### Searches

The prescribed searches were run through msearch.py under Q57 and this item;
their original result records are in sandbox `searches.jsonl`.

1. LeanFinder: “For a proper scheme over a Noetherian local ring and an invertible
   module ample on its closed fibre there is one ample twist bound making first
   cohomology of every successive maximal ideal power quotient vanish”. Eight hits,
   concerning affine-limit localization, vanishing of restricted structure sections,
   and finite H1 cotangent modules. None is this statement.
2. LeanSearch: “Uniform vanishing of H1 for all conormal layers of the closed fibre
   of a proper scheme twisted by powers of a fibre ample line bundle”. Eight hits,
   including formally smooth/etale H1 cotangent vanishing, localization and proper
   global sections finiteness. None is this statement.
3. Loogle: `AlgebraicGeometry.IsProper`. Twelve properness declarations/instances;
   none states uniform twisted cohomology vanishing.
4. Mathlib grep via msearch: `graded.*vanish|vanish.*graded|conormal.*cohomolog`,
   subdirectory AlgebraicGeometry: zero hits.
5. Project rg: `lem-trf-fibre-conormal-uniform-vanishing|fibre_conormal_uniform_vanishing|conormal.*vanishing|vanishing.*conormal`
   in `lean/WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`:
   only unrelated cotangent-H1/conormal and lci references; no exact declaration
   or declaration using this blueprint id. Additional searches of ideal powers,
   formalModuleQuotient, tensorPullback and IsAmple located the reused interfaces.

No STATEMENT-DISPUTED flag, statement correction, new node, or dependency repair.
The first compile diagnosed unqualified `pullback` resolving to Modules.pullback;
qualified the scheme product as `Limits.pullback`. The next prescribed scompile.py
run passed both sandbox and library mode with no errors or non-sorry warnings.

## Second reading by Q57

Reopened the node and the complete final Lean file for a separate self-audit.
The dispatcher explicitly forbids starting another agent; this is a second reading
by the author, not a claim of an independent worker review. The maintainer's
independent review remains required by the delivery protocol.

Matched each hypothesis and clause using the table above. In particular: the closed
fibre is the literal A/m pullback; its first projection is used for the ample
hypothesis; J is canonically extended, not quantified as an arbitrary ideal;
the quotient has numerator J^n and denominator J J^n; n = 0 is O_X/J; the tensor
power is nonnegative with unit at zero; cohomology is the prescribed module
cohomology in degree one; the existential bound precedes both indices. No extra
Noetherian-scheme, flatness, nonempty, positive-index or invertibility hypothesis
was introduced. The fibre invertibility proof is furnished by the existing theorem.
The node's statement, dependencies, proof and metadata remain unchanged except lean.
The only correction during drafting was qualification of scheme pullback, already
confirmed by compilation. No mathematical mismatch was found.
