## Worker report

The module `Sheaf.AlgebraicGeometry.TraitSpecialNeutralFiniteTypeOpen` states
`AlgebraicGeometry.exists_trait_specialNeutral_finiteType_open`, with proof `sorry`.
It introduces no definitions and changes only the item's `lean` record. The theorem's
docstring contains all seven steps of the accepted natural-language proof, including
the two-fibre quasi-compactness argument, ramified overlap argument, and smooth lifting.

Hypotheses and clauses, in order:

- A DVR is `(A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]`.
  Its spectrum is `Spec (.of A)`; `L`, `[Field L]`, `[Algebra A L]`, and
  `[IsFractionRing A L]` specify its fraction field. The residue field is the canonical
  `IsLocalRing.ResidueField A`, with quotient map `IsLocalRing.residue A`. Choosing
  this actual residue field is notation for the node's k, rather than an extra hypothesis.
- `J : Over (Spec (.of A))` and `[GrpObj J]` specify the group scheme, including
  its multiplication, unit, inverse, and diagrams. `[Smooth J.hom]`,
  `[IsSeparated J.hom]`, and `[LocallyOfFiniteType J.hom]` give the three hypotheses.
  Mathlib's `IsSeparated` is defined by the closed-immersion condition on the diagonal.
- The two instances on `pullback.snd J.hom (Spec.map (CommRingCat.ofHom
  (algebraMap A L)))` give local finite type and quasi-compactness of the actual
  generic fibre, hence exactly finite type. There is no quasi-compactness hypothesis
  on J, Neron condition, commutativity, or field-perfection assumption.
- The existential `C` is an open of the actual special-fibre base-change object.
  Its first equality identifies its underlying subset with
  `connectedComponent (GrpObj.onePoint ...)`, so it is exactly the identity component
  with its open-subscheme structure, without replacing it by a reduced subscheme.
- `U : J.left.Opens` has subset the complement of the image under `pullback.fst`
  of the complement of C. This is precisely `J \ (J_k \ J_k^0)`.
- `gU : GrpObj (Over.mk (U.ι ≫ J.hom))` and `IsMonHom` for `Over.homMk U.ι`
  give the compatible subgroup structure. Its inclusion is the canonical open immersion,
  hence a monomorphism. A group homomorphism also preserves inverse.
- `Smooth`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` of
  `U.ι ≫ J.hom` give the asserted properties, with the last two expressing finite type.
- The generic pullback projection has preimage of U equal to `Set.univ`; the special
  pullback projection has preimage of U equal to C. These identify the canonical
  open subschemes, and therefore their restricted structure sheaves: U_L is all of J_L,
  and U_k is exactly C. Equality of subsets suffices because these are open subschemes
  with their actual restriction structure, not arbitrary schemes with the same points.
- `∀ (K : Type u) [Field K] [Algebra (IsLocalRing.ResidueField A) K]` expresses
  every residue-field extension. The preimage of C under its actual base change equals
  the connected component of the identity of the base-changed group. This expresses
  `(J_k^0)_K = (J_K)^0` as equality of open subschemes, with no reducedness assumption.
- The B-clause quantifies a DVR B, a ring map `φ : B →+* A`, faithful flatness
  `φ.FaithfullyFlat`, and the recorded `Over.DescentDatum (Spec.map ...) J`.
  The next two implications are compatibility of its transport with multiplication
  and unit, exactly as in the upstream group-scheme descent API. Since transport is
  bijective, this also preserves inverse; it imposes precisely group compatibility.
- `D.toHom ⁻¹' U = pullback.fst ... ⁻¹' U` is the overlap-invariance clause in the
  recorded descent API's universal-transport presentation. The source of `D.toHom` is
  `J ×_(Spec B) Spec A`, canonically the pullback of J to
  `Spec A ×_(Spec B) Spec A = Spec (A ⊗[B] A)`. Its `pullback.fst` is the original
  J-coordinate, and `D.toHom` is the transported J-coordinate. Thus the equality is
  exactly that the descent isomorphism identifies p0*U and p1*U, including their open
  scheme structures even on a nonreduced overlap. No arbitrary comparison map is chosen.
- The final implication assumes exactly `IsStrictlyHenselianLocalRing A`.
  A section is `l : 𝟙_ (Over (Spec (.of A))) ⟶ J`, the same as a T-section T → J.
  The explicitly written composite `lift (toUnit J ≫ l) (𝟙 J) ≫ μ[J]` is left
  multiplication by l. Its restriction along U.ι is asserted to be an open immersion,
  and `∀ x, ∃ l, x ∈ ... '' U` asserts precisely that these images cover J.

All universes are explicitly declared and all binders explicit; auto-implicits are
disabled. Rings and schemes share the standard ambient universe u, as in the recorded
scheme/base-change interfaces; no independent smaller test universe is introduced.
The standard scoped `CategoryTheory.Obj` instance constructs base-changed group
structures via `Functor.grpObjObj`; this is an existing global scoped instance,
not a new local instance or a new group construction.

Dependency declarations read and used:

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`.
- `Mathlib.AlgebraicGeometry.Scheme`: `Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, together
  with `QuasiCompact` from `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.Separated`: `IsSeparated` (closed diagonal).
- `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`: recorded scheme
  base change is `Over.pullback`, with scheme `Limits.pullback` and its projections.
  The recorded module-pullback declaration is not the scheme-base-change notion;
  its record explicitly prescribes these projections, which are used here.
- `Mathlib.Topology.Connected.Basic`: `connectedComponent`, `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `IsOpenImmersion` and canonical opens.
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`;
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat`.
- `WeilConjectures.CategoryTheory.Comma.Over.DescentDatum`: `Over.DescentDatum`,
  its full transport/cocycle interface, and its canonical `toHom`.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Basic`: `GrpObj.onePoint`;
  `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Functor.grpObjObj`;
  `Mathlib.CategoryTheory.Monoidal.Mon`: `IsMonHom`, unit and multiplication.

The module also imports the recorded proof-dependency modules for the smooth-fibre
criterion, fibre-component neighbourhood, density of rational points, henselian
smooth-algebra lifting, finite presentation, scheme fibres, affine morphism
correspondence, and affine ring-map comparison. The proof node
`lem-sfb-lft-field-group-neutral-component` currently has no Lean module, so there
is no module to import for it. It is used in the natural-language proof but is not
required to type this statement. No missing definition is hidden behind it.

Edge checks: a group scheme cannot be empty, since its identity section exists over
the nonempty trait. For the trivial group U is J and both fibres are the identity.
For a group with connected special fibre the complement formula gives U = J. For
disconnected special fibre it deletes exactly the other special components and keeps
the entire generic fibre. Non-quasi-compact J is allowed. Inseparable extensions,
positive residue characteristic, ramified faithful-flat maps, nonreduced overlaps,
and the identity descent datum are all included. The translate clause is conditional
on strict henselianity only, with no separable-closedness hypothesis elsewhere.

Searches for an exact existing statement:

- `msearch.py ... leanfinder`: “A smooth separated locally finite type group scheme
  over a DVR has an open finite type subgroup given by the generic fibre and the
  special identity component”; eight hits, concerning smooth/unramified loci,
  finite fibres, Jacobson spaces, and topological local rings; no matching theorem.
- `msearch.py ... loogle '"GrpObj", "IsOpenImmersion"'`: zero hits.
- `msearch.py ... grep 'specialNeutral|neutralComponent|neutral_component'
  AlgebraicGeometry`: zero Mathlib hits.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `specialNeutral|special_neutral|trait.*neutral`: no exact statement.
- Broader `rg` for group components located
  `Sheaf.AlgebraicGeometry.LocallyAlgebraicGroupIdentityComponent` and
  `Sheaf.AlgebraicGeometry.GroupNeutralComponentTranslates`. Their full statements
  were read: the former assumes an algebraically closed base field; the latter is
  a finite-type field-group result. Neither states the trait construction, faithful-flat
  descent invariance, or strict-henselian translate cover. The existing field-only
  `GrpObj.mulLeft` is expanded using the same standard categorical formula over A;
  no second translation definition is introduced.

Primary source checked: the online Numdam scan of Raynaud, printed pp.40-42,
especially p.42 (3.3.4) and the preceding smooth translate-cover paragraph;
`literature/stacks-project/groupoids.tex`, proposition-connected-component (0B7R).
No statement correction or dispute was needed.

## Second reading by Q128

I reread the source node and the complete signature after drafting, separately checking
the hypotheses and every conjunct against the mapping above. This is a self-audit;
no independent agent was started, as the dispatcher brief prohibits it. In particular,
I checked that C is the actual special-fibre open component rather than its reduction,
that the generic fibre is unrestricted, that the descent transport compares the two
trait maps rather than just identity descent, and that the cover uses all A-sections.
The compiler checks required the standard scoped base-change group instance and an
explicit `SetLike.coe C` coercion for the identical underlying pullback scheme. Neither
changes the mathematical statement. The maintainer's independent review remains the
independent reading of this delivery.

Validation: `scompile.py Q128 lem-sfb-trait-special-neutral-finite-type-open` compiled
the file in sandbox mode and under its final library module name with no errors or
warnings (14.3 s and 9.5 s respectively). Only the main theorem is postponed.
