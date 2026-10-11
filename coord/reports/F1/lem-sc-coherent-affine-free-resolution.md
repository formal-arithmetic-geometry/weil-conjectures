## Worker report

The module `Sheaf.AlgebraicGeometry.CoherentAffineFreeResolution` states
`AlgebraicGeometry.coherent_affine_free_resolution`, with a single `sorry` and no new definitions.
The node is unchanged except for its `lean` field. No dependency record needs repair.

Hypotheses and clauses:

- `X : Scheme.{u}` is the scheme; `[IsNoetherian X]` is exactly the conjunction of
  `IsLocallyNoetherian X` (pqf-def-locnoeth) and `CompactSpace X`
  (def-weil-pbc-quasi-compact-scheme), by Mathlib's class declaration.
- `F : X.Modules` is the O_X-module and
  `hF : RingedSpace.IsCoherent X.toRingedSpace F` is precisely pqf-def-coherent.
- `x : X` is the given point; the conclusion quantifies `U : X.Opens` and `x ∈ U`.
- `IsAffineOpen U`, a commutative ring `A`, and `e : U.toScheme ≅ Spec (CommRingCat.of A)`
  express the affine neighbourhood U = Spec A. `IsNoetherianRing A` states the requested
  Noetherianity of its coordinate ring.
- `M : Type u`, `AddCommGroup M`, `Module A M`, `Module.Finite A M` introduce precisely
  the finite A-module. A finite module over A can be represented in the universe of A;
  no size restriction on the mathematical finite module is imposed.
- `Nonempty (F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj
  (tilde (ModuleCat.of A M)))` is F|_U ≅ M~. Restriction along the isomorphism e transports
  M~ from Spec A to U. No arbitrary sheaf takes the place of tilde.
- `E : CochainComplex (SheafOfModules ((moduleRings X.toRingedSpace).over U)) ℤ`
  is a cochain complex of O_U-modules on the localized open site.
- `∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (E.X i)` is bounded above, not bounded on both sides.
- `∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free ... (ULift (Fin r)))`
  says that every term is free of finite rank, with degree-dependent rank.
- `∃ q : E ⟶ (CochainComplex.singleFunctor ... 0).obj (F.over U), QuasiIso q`
  supplies the actual augmentation E → F|_U[0] and its quasi-isomorphism property.
  Mathlib's `Scheme.Modules.overEquiv U` and `overFunctorEquiv U` identify the localized
  open-site restriction `F.over U` with `F.restrict U.ι`; these are two established
  presentations of the same restriction, not different mathematical sheaves.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Noetherian`: `IsLocallyNoetherian`, `IsNoetherian`.
- `Mathlib.Topology.Defs.Filter`: `CompactSpace` (included by the Noetherian imports).
- `Sheaf.AlgebraicGeometry.Coherent`: `AlgebraicGeometry.RingedSpace.IsCoherent`.
- `Mathlib.AlgebraicGeometry.Modules.Tilde`: `AlgebraicGeometry.tilde`,
  `tilde.adjunction`, the unit IsIso instance, and
  `Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent`; tilde is used in the signature.
- `Sheaf.RingTheory.FiniteFreeResolution`: `Module.exists_finite_free_resolution`, read
  in full; used in the natural-language proof plan, not required to type the signature.
- `Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine`:
  `Scheme.Modules.quasicoherent_finite_type_affine`, read in full; used in the proof plan,
  not required to type the signature. These two theorem-only imports are omitted as unused.

The file also uses Mathlib's `Scheme.Modules.restrictFunctor`, `SheafOfModules.free`,
`CochainComplex.singleFunctor`, `HomologicalComplex.QuasiIso`, and `IsZero`.

Edge cases checked before finalization: the empty scheme has no x, so the implication is
vacuous there; zero F and zero M are allowed; rank zero is allowed by Fin 0; the bound N
is arbitrary; the negative degrees can be infinite, as required for a nonregular
Noetherian ring. Neither a regularity hypothesis nor a finite-length resolution is assumed.
The ring and modules use the scheme's universe u; the small finite module can be chosen
in this universe and ULift only lifts its finite free basis indices.

Searches for an existing statement:

- `msearch.py leanfinder "coherent sheaf on Noetherian affine scheme admits bounded above
  finite free resolution"`: eight hits, for `SheafOfModules.IsFiniteType` and Noetherian
  scheme/affine-cover facts; no resolution statement.
- `msearch.py loogle "IsNoetherian, tilde, QuasiIso"`: zero hits, unknown identifier tilde.
- `msearch.py grep "finite.*free.*resolution|coherent.*resolution" AlgebraicGeometry`:
  zero hits in Mathlib.
- `msearch.py leansearch "coherent sheaf bounded above resolution by finite rank free
  modules on affine Noetherian scheme"`: service unavailable, Internal Server Error.
- `rg` in WeilConjectures for finite-free/coherent resolutions and the item id: the
  projective-line resolution by twists is a different statement; no generic affine result.
- `rg` in lean/Sheaf: the module finite-free theorem and bounded-above Hom-acyclicity
  theorem exist, but no theorem providing this affine coherent-sheaf resolution.
- `rg` of the proposed full name in dag/lean_names_upstream.json and source trees:
  no existing declaration of `AlgebraicGeometry.coherent_affine_free_resolution`.

Local literature/stacks-project is absent on this machine. Read the source instead at
[Stacks 01XZ](https://stacks.math.columbia.edu/tag/01XZ) and
[Stacks 00LP](https://stacks.math.columbia.edu/tag/00LP): the former supplies the affine
finite-module description, and the latter supplies the unbounded finite-free resolution.
No STATEMENT-DISPUTED issue or node fault was found. The declaration docstring contains
all three proof steps, citing their DAG dependencies. The first server compile exposed
namespace and integer-single-complex spelling issues; after fixing them it compiled cleanly.

## Second reading by F1

I independently read the node statement and the Lean signature item by item. The node's
Noetherian scheme is rendered by `(X : Scheme.{u}) [IsNoetherian X]`; Mathlib's
`IsNoetherian` extends exactly `IsLocallyNoetherian` and `CompactSpace`, matching the two
cited hypotheses. The coherent module and point are rendered by `(F : X.Modules)`,
`hF : RingedSpace.IsCoherent X.toRingedSpace F`, and `(x : X)`, with no extra hypotheses.

The existential affine neighbourhood is rendered by `U : X.Opens`, `x ∈ U`,
`IsAffineOpen U`, a commutative ring `A : Type u`, `IsNoetherianRing A`, and
`e : U.toScheme ≅ Spec (CommRingCat.of A)`. Thus the Lean isomorphism supplies precisely
the node's notation `U = Spec A`, without choosing a special affine open or adding a
separation or regularity assumption. The finite module is rendered by `M : Type u` with
`AddCommGroup M`, `Module A M`, and `Module.Finite A M`; the universe is the scheme/ring
universe and does not exclude the witness obtained from sections.

The clause `Nonempty (F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj
(tilde (ModuleCat.of A M)))` is exactly the node's isomorphism
`F|_U ≅ \\widetilde M`: `e.hom` transports the tilde module from `Spec A` to `U`.
The final existential uses `E : CochainComplex
(SheafOfModules ((moduleRings X.toRingedSpace).over U))`, the localized presentation of
O_U-modules, and `F.over U` in the same presentation. Its three conjuncts render all
conclusion clauses: `∃ N : ℤ, ∀ i, N < i → IsZero (E.X i)` is bounded above; every degree
has a finite rank `r : ℕ` and an isomorphism to `SheafOfModules.free ... (ULift (Fin r))`;
and `∃ q : E ⟶ (CochainComplex.singleFunctor ... 0).obj (F.over U), QuasiIso q` is the
degree-zero augmentation and quasi-isomorphism. The quantifier order agrees with the node.

No mismatch was found, so no source or Lean statement was changed. I checked the empty
scheme (the point hypothesis makes the assertion vacuous), zero modules and rank zero,
arbitrary negative degrees in the bounded-above complex, and `n = 0`; no case is excluded.
The characteristic is unrestricted. I repeated searches in Mathlib, the source project,
the DAG name index, and `lean/Sheaf` for coherent affine finite-free resolutions; only
the present declaration and generic finite-free module infrastructure were found. The
server single-file compile completed cleanly, with only the intended `sorry` proof.
