## Worker report

The module states `AlgebraicGeometry.exists_normal_projective_compactification_over_complete_trait`.
Only this named theorem is postponed, with `sorry`. No definition or statement was changed,
no additional node is needed, and there is no statement dispute. Its docstring contains all
ten proof steps of the node, including their dependency references.

The source was read in ILO, Expose XVI 3.7, first paragraph, printed p.254 (PDF page 260):
regular integral quasi-projective flat X over a strictly henselian mixed-characteristic trait;
extend the trait to the algebraic constants in its function field, then normalize its
projective closure. The conclusion retains X, rather than its base change. The complete
case of this preparation is the node's statement.

Clause-by-clause correspondence:

- `R : Type u`, `CommRing R`, `IsDomain R`, `IsDiscreteValuationRing R` give S = Spec R.
  Mathlib's DVR is a nonfield local PID, equivalently the dimension-one Noetherian local
  domain with principal maximal ideal specified in the node. It includes Noetherianity.
- `IsStrictlyHenselianLocalRing R` means henselian with separably closed residue field;
  `IsAdicComplete (IsLocalRing.maximalIdeal R) R` is maximal-ideal-adic completeness.
- `CharZero R` and `hMixed : ringChar (IsLocalRing.ResidueField R) ≠ 0` render mixed
  characteristic. For a domain, R and its fraction field have the same characteristic;
  the residue field has prime characteristic, so nonzero characteristic is positive.
- `X : Scheme.{u}`, `IsIntegral X`, `hRegular : IsRegularScheme X`, `f : X → Spec R`
  are the original integral regular S-scheme. The regular predicate includes local
  Noetherianity and uses the upstream stalkwise regularity class.
- `Flat f`, `LocallyOfFiniteType f`, `QuasiCompact f` are flatness and finite type.
- `hQuasiProjective` is exactly a locally closed immersion (`IsImmersion`) into projective
  space with finite homogeneous coordinate type, commuting with f. A finite nonempty
  coordinate type is equivalent to Fin (N+1). An empty coordinate type has empty
  projective space and cannot contain this nonempty integral X. Consequently this
  formulation excludes no case and adds none. The upstream `IsQuasiProjective` accepts
  only field bases, so the supplied relative definition is expanded inline, not copied
  into a new private predicate.
- The existential `R₀` has a commutative domain structure, DVR, strict henselianity,
  and maximal-ideal-adic completeness. `t : Spec R₀ → Spec R`, `IsFinite t`, and
  `IsDominant t` give the finite dominant extension of complete strictly henselian traits.
- `C : Scheme.{u}`, `IsIntegral C`, `q : C → Spec R₀`, `IsHProjective q` give the
  integral projective S₀-scheme, in the dependency's finite projective-space convention.
- `∀ c, IsDomain (C.presheaf.stalk c) ∧ IsIntegrallyClosed (C.presheaf.stalk c)` is
  the stated normality, and `Flat q` is flatness of the new structural morphism.
- `j : X → C`, `IsOpenImmersion j`, `DenseRange j` give the dense open immersion of
  the original X. `j ≫ q ≫ t = f` is its being over S. No X ×_S S₀ occurs.
- The generic fibre is the pullback of q along the canonical generic-point morphism
  `(Spec R₀).fromSpecStalk (genericPoint (Spec R₀))`. `GeometricallyIntegral` of its
  projection to Spec k(S₀) means integrality after every field extension.
- Mathlib's `Scheme.functionField` is definitionally the structure-sheaf stalk at
  `genericPoint`; it is a field for integral schemes. Thus k(S), k(S₀), k(X), k(C)
  have precisely the meaning stipulated in the node, using the recorded generic point
  and stalk construction. No new function-field object is introduced.
- `e : C.functionField ≃+* X.functionField` is the field identification. Its equation
  with `fromSpecStalk` and j forces it to be induced by this embedding, rather than
  an unrelated isomorphism. Likewise a and b are field embeddings from k(S) and k(S₀)
  into k(X); their two scheme-map equations force exactly the maps induced by f and jq.
  A ring homomorphism between fields is automatically injective. The equations, together
  with the structural triangle, also force compatibility with t.
- Finally, for every z in k(X), `@IsAlgebraic ... a.toAlgebra z ↔ z ∈ Set.range b`
  says precisely that k(S₀) is the subfield of all elements algebraic over K = k(S).
  No arbitrary algebra structure, independent field extension, or function-field
  replacement is admitted. `a.toAlgebra` explicitly specifies the canonical embedding
  used by the algebraicity predicate, without a hidden `let`.
- The closing sentences defining etale, smooth and other geometric properties introduce
  no extra assumption or conclusion. Their recorded modules are imported as prescribed.

Dependency declarations used (source signatures and docstrings read):

- `def-pc-integral-scheme`: `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral`.
- `def-weil-regular-scheme`: `Sheaf.AlgebraicGeometry.IsRegularScheme`, `AlgebraicGeometry.IsRegularScheme`.
- `def-weil-flat-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`.
- `def-weil-finite-type-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-finite-integral-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite`.
- `def-kun-projective`: `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective`.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`, `AlgebraicGeometry.Etale`.
- `def-pc-geometrically-irreducible`: `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral`.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`.
- `def-sc-generic-point`: `Mathlib.Topology.Sober`, `IsGenericPoint`.
- `def-weil-pbc-module-stalk`: `WeilConjectures.Topology.PresheafModuleStalkFunctor`, `PresheafOfModules.moduleStalkFunctor`.

`Mathlib.AlgebraicGeometry.FunctionField` supplies the existing stalk abbreviation and its
field structure; `Mathlib.AlgebraicGeometry.Morphisms.Immersion` supplies the locally closed
immersion; `WeilConjectures.AlgebraicGeometry.ProjectiveSpace` supplies projective space;
`Mathlib.RingTheory.DiscreteValuationRing.Basic`, `Mathlib.RingTheory.AdicCompletion.Basic`,
and `WeilConjectures.Mathlib.RingTheory.Henselian` supply the exact ring predicates.
The listed statement modules are public imports. Every proof dependency with a recorded
Lean module is imported, privately when not already a statement import. Proof dependencies
without such a record do not create additional assumptions in the statement.

Edge cases checked before writing: integral excludes the empty X and empty C; a field is
not a DVR; residue characteristic zero is explicitly excluded, while every positive prime
is allowed. Zero-dimensional generic fibres and the identity extension of traits are allowed.
The open immersion need not be surjective; it may be an isomorphism. R₀ is not assumed
etale or unramified. No condition of surjectivity or nonempty closed fibre is imposed on X.
All rings and schemes use the arbitrary common universe u; finite extensions and finite-type
closures remain in this universe, and geometric integrality uses Mathlib's unrestricted
geometric predicate (field extensions tested in the scheme universe suffice). No universe
is auto-bound (`set_option autoImplicit false`).

Searches for an existing statement:

- msearch.py leanfinder: "normal integral projective compactification over complete strictly
  henselian trait with algebraic constants" returned eight hits on relative normalization,
  Proj properness, and global sections, none including the compactification with constants.
- msearch.py loogle: "AlgebraicGeometry.IsHProjective, IsDiscreteValuationRing" returned zero
  hits, reporting unknown identifier IsHProjective (the latter is upstream, not Mathlib).
- msearch.py grep: `compactification|IsQuasiProjective|IsNormal`, AlgebraicGeometry, zero hits.
- Direct rg in Mathlib, WeilConjectures, and lean/Sheaf for IsQuasiProjective, IsNormal,
  functionField, trait, and completeness located the reusable notions above, and the
  upstream field-only quasi-projectivity definition, but no theorem with this conclusion.
- Direct rg for the item id in upstream WeilConjectures and lean/Sheaf returned no match.
- Current published sources for the recorded Projective and PresheafModuleStalkFunctor
  modules were read with scompile.py --source because the old local checkout lacks them.

Validation uses only scompile.py, separately checking sandbox and final library module names.
The first pass elaborated the full statement; its sole style warning was an extra blank
line at the end of the theorem docstring, removed before the final pass.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
