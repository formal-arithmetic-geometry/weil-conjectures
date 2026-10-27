## Worker report

The delivery states `AlgebraicGeometry.EquivariantCoherent.torus_nonfixed_complement_annihilation`
in `Sheaf.AlgebraicGeometry.TorusNonfixedComplementAnnihilation`. Its only new postponed
proof is this theorem, with `sorry`; its docstring reproduces all seven accepted proof steps.
The auxiliary definition module has no postponed proofs and no choices of data.
The natural-language statement, source, proof and proof dependencies are unchanged.
The statement dependencies gain only the new definition node described below.

Hypothesis and clause correspondence:

- The field is `(F : Type u) [Field F]`, and algebraic closedness is `[IsAlgClosed F]`.
  The universe is explicit and unrestricted; the test algebras have the same universe as F.
- The generic opening conventions for affine group schemes, rational representations,
  coherent linearizations, integral G-zero and tensor action are the existing definitions,
  not extra hypotheses or a second definition. `RationalRepresentationGZero` publicly
  exposes `Representation`, `RationalModule`, `IsRepresentationRelation`,
  `RepresentationGZero`, `IsRepresentationRing`, `IsAssociated`, and
  `IsRepresentationAction`. In particular the coaction is counital/coassociative and
  the associated-bundle convention uses the forward geometric action. The actual
  theorem specializes to the stated T and its character ring; it does not claim a
  separate annihilation theorem for arbitrary G.
- `(r : ℕ)`, `(T : Grp (Over (Spec (.of F))))`, and
  `hT : Nonempty (T ≅ MultiplicativeType.splitTorus F r)` say exactly split torus,
  allowing rank zero. The split torus is the existing finite product of the recorded
  multiplicative group, which represents units. Affineness and finite type of T are
  consequences of this split form, not additional restrictions on T.
- `(Y U : CategoryTheory.Mod (Over (Spec (.of F))) T.X)` supplies algebraic actions
  with the actual unit and associativity identities. The classes
  `[IsSeparated Y.X.hom] [LocallyOfFiniteType Y.X.hom] [QuasiCompact Y.X.hom]`
  express separated and finite type, using the recorded dependency conventions.
- `(W : Over (Spec (.of F))) (i : W ⟶ Y.X) [IsClosedImmersion i.left]`
  is the stated closed immersion. `hfixed` says precisely that a point factors
  through i iff it is fixed after every further commutative algebra extension.
  Both quantifiers `A`, `B`, the arbitrary algebra morphism `f`, and all `t` are
  retained. It tests the scheme functor, including nonreduced algebras, rather than
  just F-points. Uniqueness of the factorization follows because a closed immersion
  is a monomorphism.
- `(j : U ⟶ Y) [IsOpenImmersion j.hom.left]` is an equivariant open immersion.
  `hcomplement : Set.range j.hom.left = (Set.range i.left)ᶜ` identifies its image
  with exactly Y minus W. An open immersion with this image is the induced open
  subscheme up to its unique isomorphism, and equivariance makes its action induced.
- `D : ActionGroupoidModel T.X U.X` uses the recorded presentation, with source,
  target, identity, inverse, group-coordinate-normalized composition, and all laws.
  `Coherent D` and `GZero D` are the existing coherent linearized modules and
  quotient by equivariant isomorphisms and every short exact sequence. Their
  linearization is `a^*M ≅ p^*M`; its inverse is the action from y to ty.
- `TrivialTorusCoherent.Character T` is exactly the additive version of group-scheme
  morphisms to G_m; `CharacterRing T` is `AddMonoidAlgebra ℤ` on these characters.
  Thus the coefficient ring is integral, and `single χ 1` is exactly e^χ.
- `[m : Module (CharacterRing T) (GZero D)]` together with `hm : IsCharacterAction D m`
  specifies the character action, following the existing representation-action
  interface style. It is not an arbitrary module structure: all character twists
  must exist, and its value on every generator and every twist is fixed. In the new
  `IsCharacterTwist` definition the inverse linearization of P is transported by e
  and equals χ(pr_1) times the inverse linearization of M. This is tensor by F_χ,
  with the positive forward sign, valid over the entire scheme T times U.
- `(α : GZero D)` quantifies over every class. The conclusion gives `n : ℕ` and
  `χs : Fin n → Character T`, with every `χs k ≠ 0`, and exactly
  `(∏ k, (1 - AddMonoidAlgebra.single (χs k) 1 : CharacterRing T)) • α = 0`.
  Repetitions are allowed. For n=0 the Fin-indexed product is 1.
- There is no smoothness, properness, stabilizer reduction, characteristic restriction,
  rational scalar extension, or division in the signature.

Dependency declarations read and used:

- Mathlib.Algebra.Field.Defs: `Field`.
- Mathlib.FieldTheory.IsAlgClosed.Basic: `IsAlgClosed`.
- Mathlib.CategoryTheory.Monoidal.Grp: `GrpObj`, bundled by `Grp`; Mathlib's cartesian
  `ModObj`/`Mod` and equivariant morphisms encode algebraic actions.
- Mathlib.AlgebraicGeometry.Scheme: `Scheme`, `Scheme.Hom`, and `Over` schemes.
- Sheaf.AlgebraicGeometry.CoherentFiniteType and WeilConjectures.AlgebraicGeometry.Coherent:
  the recorded finite-type predicate and exact `RingedSpace.IsCoherent` (finite type
  and finite-type kernels). The latter is used through `Coherent D`.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: `IsSeparated`, without `IsProper`.
- Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact:
  `LocallyOfFiniteType`, `QuasiCompact`.
- Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion: `IsClosedImmersion`.
- Mathlib.AlgebraicGeometry.OpenImmersion: `IsOpenImmersion`.
- Sheaf.AlgebraicGeometry.EquivariantCoherentGZero: `ActionGroupoidModel`, `Coherent`,
  `underlying`, `linearization`, `classOf`, `GZero`, as imported by the existing
  rational representation module. The full groupoid-module identity and cocycle
  definitions in SchemeGroupoidModule were also read.
- Sheaf.AlgebraicGeometry.TrivialTorusCoherentData: `Character`, `CharacterRing`,
  `characterValue`; only these shared notions are used, not its trivial-base
  `Linearization` or its distinct group presentation.
- Sheaf.AlgebraicGeometry.ToriMultiplicativeType: `MultiplicativeType.splitTorus`.
- The proof dependency `exists_torus_invariant_affine_filtration` is read in full
  and imported non-publicly. `lem-sfb-equivariant-coherent-localization-sequence`
  currently has no Lean record or Mathlib match, so it has no available proof import;
  it remains explicitly cited by id in the theorem docstring and unchanged proof plan.

Edge cases checked before writing and again against the signature:

- r=0 gives the trivial group, W=Y, U empty, α=0, and n=0 is allowed.
- Empty Y, empty U, zero α and the empty character list are permitted.
- W empty is permitted for fixed-point-free actions; the complement may be all Y.
- Weight p in characteristic p remains a nonzero group-scheme character: no
  differential or finite group of F-points replaces it. μ_p stabilizers are allowed.
- Nonreduced Y and W and arbitrary singular separated finite-type Y are permitted.
- Zero modules and the zero character are allowed in the twist definition (the
  latter gives the untwisted action); only annihilator factors require χ nonzero.
- For a point and a pure character line, the formula multiplies the forward action
  by χ(t), checking that the sign is positive, as required by the node.
- The fixed-point condition includes all algebra morphisms, including identities,
  nilpotent extensions, and zero test algebras.

Sources read: Milne iAG2017 Theorem 22.50 at printed p.480 and its proof invoking
Nielsen/Iversen; the latest blueprint direct-images statement and proof (3). These do
not purport to prove this supporting concentration lemma. The accepted agent proof and
WANTED Thomason attribution are retained. Stacks groupoids linearization definitions
are the source for the formula, not a claimed source for the concentration theorem.
No statement correction or STATEMENT-DISPUTED issue was found.

Searches actually run (msearch.py, with raw records logged):

- leansearch: `Split torus equivariant coherent Grothendieck group character action annihilation nonfixed locus`; 8 hits; SubMulAction.ofFixingSubgroup_equivariantMap, Representation.toCoinvariants_mk, Representation.Coinvariants.mk_self_apply, instSMulCommClassQuotientSubgroupSubtypeMemSubalgebraSubalgebra, instMulSemiringActionQuotientSubgroupSubtypeMemSubalgebraSubalgebra, instMulSemiringActionQuotientSubgroupSubtypeMemSubringSubring, fixedPointsSubAddOfNormal, Representation.FiniteCyclicGroup.coinvariantsEquiv.

- leanfinder: `Product of one minus nonzero torus characters annihilates equivariant coherent G zero classes`; 8 hits; ContinuousCohomology.kerHomogeneousCochainsZeroEquiv, UnitAddTorus.mFourier_zero, BoundedContinuousFunction.char_zero_eq_one, Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff, FDRep.scalar_product_char_eq_finrank_equivariant, AddChar.wInner_cWeight_eq_zero_iff_ne, MeasureTheory.Measure.addModularCharacterFun_map_zero, MeasureTheory.Measure.addModularCharacterFun_map_add.

- loogle: `AddMonoidAlgebra.single, Module`; 6 hits; AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.mapDomainLinearMap_single, AddMonoidAlgebra.uniqueLinearEquiv_symm_apply, AddMonoidAlgebra.mapDomainLinearEquiv_single, AddMonoidAlgebra.counit_single, AddMonoidAlgebra.comul_single.

- grep: `equivariant.*(coherent|GZero)|character.*annihil`; 0 hits; no matches.

- leansearch: `Tensor by a group scheme character defines an action of its integral character ring on equivariant coherent Grothendieck group`; 8 hits; FDRep.char_tensor, FDRep.scalar_product_char_eq_finrank_equivariant, CharacterModule.int, CharacterModule, Rep.homEquiv, Representation.Coinvariants.mk_inv_tmul, Rep.MonoidalClosed.linearHomEquiv, CharacterModule.congr.

- leanfinder: `Character twist of coherent sheaf linearization on scheme with algebraic torus action`; 8 hits; ModuleCat.tilde, Rep.instMonoidalActionTypeLinearization, AlgebraicGeometry.Scheme.Modules.map_smul, AlgebraicGeometry.Scheme.Modules.pullback, AlgebraicGeometry.Scheme.Modules.Hom.app_smul, AlgebraicGeometry.Scheme.Modules.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf, AlgebraicGeometry.Scheme.Modules.pseudofunctor_obj_obj, AlgebraicGeometry.Scheme.Modules.pseudofunctor_map_l.

- grep: `IsCharacterTwist|IsCharacterAction|character.*twist`; 2 hits; Mathlib/NumberTheory/LSeries/Dirichlet.lean, Mathlib/NumberTheory/LSeries/Dirichlet.lean.

The returned representation/coinvariant and ordinary module-pullback declarations do
not state the annihilation theorem or the general-base coherent character action.
Direct rg searches for the item id and for `character.*(twist|action)`,
`IsCharacterTwist`, `IsCharacterAction`, torus/coherent/GZero keywords in both
WeilConjectures and Sheaf found the recorded shared definitions and the trivial-base
CoherentGroupPresentation.IsTwist, not the missing general-base interface. The latter
requires a trivial base action and is unusable on the nonfixed open. A parsed search
of all DAG definition statements and blueprint_refs searches `character action` and
`character twist` found no existing node for this general-base twist/action.
blueprint_refs ancestor returned null, matching the inherited ancestry.

## New nodes

`def-sfb-torus-character-gzero-action` defines only the missing character-twist and
character-action predicates on the existing integral G-zero, in
`Sheaf.AlgebraicGeometry.TorusCharacterGZeroAction`. It imports and cites the existing
coherent group, rational coaction conventions, and shared character ring/evaluation.
The defining equality is the universal forward linearization formula
`ρ_P ≫ a^*e = p^*e ≫ ρ_M ≫ χ(pr_1)`. Both new definitions have real Prop bodies;
no object is chosen, no group or character ring is duplicated, and there is no sorry.
The source is the item's character-action convention plus Stacks 03LF/03LI.
The three focused msearch records are stored verbatim in its mathlib_searches;
project/DAG/blueprint searches are described above. Existing `IsRepresentationAction`
is normalized for a representation-ring structure, not for Z[X], and trivial-base
`IsTwist` has the wrong objects. Neither supplies this missing interface.

Validation: both modules compiled separately in dependency order through scompile.py
against the live published server build. The wrapper handled local disk exhaustion
by falling back to server compilation. Both files passed, with only the permitted
sorry on the theorem. No Lean diagnostic commands are left in the files.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
