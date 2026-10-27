## Worker report

The module `Sheaf.FieldTheory.CommonNormalCompatibleGroups` states
`Field.exists_common_normal_compatible_groups`, with its entire proof `sorry`.
It supplies no new definitions and changes only the item's `lean` record.
The docstring gives all seven DAG proof steps and their dependencies.

Clause-by-clause correspondence:

| Node hypothesis or clause | Lean rendering |
| --- | --- |
| e is a field | `(e : Type u) [Field e]` |
| I is a nonempty finite set | `(I : Type w) [Finite I] [Nonempty I]` |
| F_i/e is a finite field extension | `F : I → Type v`, its field and algebra instances, and `[∀ i, Module.Finite e (F i)]` |
| J_i is a finite group | `J : I → Type z`, its group instances and `[∀ i, Finite (J i)]` |
| homomorphisms to Aut_e(F_i), possibly noninjective | `rho : ∀ i, J i →* (F i ≃ₐ[e] F i)`; there is no injectivity hypothesis |
| existence of finite normal K/e | existential `K`, `Field K`, `Algebra e K`, `Module.Finite e K`, `Normal e K` |
| simultaneous e-embeddings u_i | `emb : ∀ i, F i →ₐ[e] K`; algebra maps between fields are injective |
| A = Aut_e(K) | the literal type `K ≃ₐ[e] K` throughout |
| G = A × product J_t | the literal type `(K ≃ₐ[e] K) × (∀ t, J t)` throughout |
| pi is first projection | the existing canonical `MonoidHom.fst (K ≃ₐ[e] K) (∀ t, J t)`, not an existential homomorphism |
| A and G finite | the first two `Finite` conjuncts |
| pi surjective | `Function.Surjective` of that canonical first projection |
| compatible subset Gamma_i is a subgroup | existential `Gamma : I → Subgroup ...` with `g ∈ Gamma i ↔ g.1.toAlgHom.comp (emb i) = (emb i).comp (rho i (g.2 i)).toAlgHom` for every ambient g |
| r_i is the coordinate map | existential monoid homomorphism `r i` with `∀ i g, r i g = g.val.2 i`; thus r is fully prescribed |
| r_i surjective | `∀ i, Function.Surjective (r i)` |
| pi(ker r_i) = Aut_{u_i(F_i)}(K) as subgroups of A | `(r i).ker.map (pi.comp (Gamma i).subtype) = (emb i).fieldRange.fixingSubgroup`, with pi written out in the file |
| fixed subfield of pi(G) purely inseparable over e | `IsPurelyInseparable e (IntermediateField.fixedField pi.range)`, with pi written out |
| normal means split minimal polynomials; separability not assumed | Mathlib `Normal e K` extends algebraicity and requires splitting of every minimal polynomial; neither `IsGalois` nor `IsSeparable` occurs |

All universes are explicit: base u, field family v, finite index w, and group
family z are independent. The witness field lives in `Type (max u v)`, supporting
the usual common-overfield/compositum construction and normal closure without
identifying the input universes. A finite family of fields in Type v can be
embedded in that universe; index and group sizes do not enlarge the field.
The theorem has no `let`, local notation, hidden choice of a map, or hollow
construction. Subgroup existence plus its precise carrier equation states the
subgroup assertion without adding a separate definition or a postponed helper.

Statement dependencies read and used:

- `def-weil-field`: Mathlib `Field`, `Mathlib.Algebra.Field.Defs`.
- `def-pc-field-extension`: Mathlib `Algebra`,
  `Mathlib.Algebra.Algebra.Defs`, used with field instances.
- `def-pc-field-tower`: imported recorded module
  `Sheaf.FieldTheory.FieldTower`, declaration `FieldExtension.degree`.
  Its documentation explicitly assigns finiteness to `Module.Finite` and
  pure inseparability to Mathlib `IsPurelyInseparable`; these existing notions
  are used directly, rather than reconstructing them from the unused degree.

Other existing interfaces read: `Normal` in `Mathlib.FieldTheory.Normal.Defs`;
`AlgHom.fieldRange` in `Mathlib.FieldTheory.IntermediateField.Basic`;
`IntermediateField.fixedField`, `fixingSubgroup`, and their membership lemmas
in `Mathlib.FieldTheory.Galois.Basic`; `MonoidHom.fst` in
`Mathlib.Algebra.Group.Prod`; `Subgroup.subtype` and `Subgroup.map`.
`IsPurelyInseparable` is publicly imported from its defining Mathlib module.

All six recorded proof dependencies are imported without `public`:
`Field.exists_common_extension` from
`WeilConjectures.FieldTheory.CommonExtensionFields`;
`IntermediateField.adjoin_rank_le_of_isAlgebraic_right` from
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic`;
the normal-closure construction and its normal/finite instances from
`Mathlib.FieldTheory.Normal.Closure`;
`card_algHom_le_finrank` from `Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`;
`AlgEquiv.liftNormal` and `liftNormal_commutes` from
`Mathlib.FieldTheory.Normal.Basic`; and
`Normal.fixedField_purelyInseparable` from
`WeilConjectures.FieldTheory.NormalExtensionFixedFieldPurelyInseparable`.
The definitions/signatures were read in source, including the nonseparable
normality and fixed-field interfaces.

Source reading: the local ILO PDF, printed pp. 150–151 (PDF pages 156–157),
contains the graph enlargement and the radicial fixed-field discussion.
The finite-family enhancement is the agent-formulated statement already
accepted in this DAG. The source Stacks `fields.tex` passages read were
`lemma-lift-maps` (0BME), `lemma-normal-closure` (09DT), and
`lemma-normal-case` (030M), whose proof identifies the fixed field.
The current blueprint's stability direct-images proof was also read.

Edge cases checked mathematically before writing:

- Singleton I and F_i=e: the product, subgroup equation and both projections
  retain their exact meanings; normality includes the trivial extension.
- Trivial J_i and trivial or nonfaithful rho_i: no injectivity or faithful-action
  instance is required. Elements in the action kernel remain in the group.
- Positive-characteristic purely inseparable extensions: Aut_e(K) can be trivial;
  the fixed field is then K, and its asserted pure inseparability is appropriate.
  No separability of any extension or intermediate field has been inserted.
- Characteristic zero: the same `IsPurelyInseparable` conclusion expresses that
  the fixed field equals the base; there is no positive-characteristic binder.
- Empty I is excluded exactly by the node's stated nonempty hypothesis.
- For a kernel element, the coordinate is one, giving pointwise fixing of the
  embedded F_i; conversely pair a fixing automorphism with the identity tuple.
  The image is formed along Gamma_i → G → A, with the required subgroup types.

Searches on 2026-10-24, using the prescribed `msearch.py Q25` wrapper:

- LeanFinder: `Finite family of finite field extensions with finite group actions embeds in common finite normal extension with compatible product subgroups`.
  Eight results, including `fixedByFinite`, `FixedPoints.normal`, `galBasis`,
  `IsGaloisGroup.intermediateField`, and `IsGalois.of_equiv`; none states the
  simultaneous assertion or the specified compatible product subgroups.
- LeanSearch: `A common finite normal extension for a finite family of finite field extensions with group actions`.
  Eight results: `Normal`, `IsNormalClosure`, normal-closure instances and
  `IntermediateField.normal_iSup`; these are ingredients, not the item.
- Loogle: `IntermediateField.fixedField, IntermediateField.fixingSubgroup, MonoidHom.fst`.
  Zero results for the combined query; the declarations were found and read by rg.
- Mathlib grep: `def (fst|snd)|def fieldRange|def fixingSubgroup|def fixedField|class Normal`.
  Found existing field ranges and product projection definitions. Direct rg read
  the Galois fixed/fixing-subgroup interfaces and normality definition.
- Project rg in both `lean/WeilConjectures` and `lean/Sheaf`, and in
  `dag/lean_names_upstream.json`: `common.normal|compatible.*[Gg]roup|lem-sfb-common-normal-compatible-groups`.
  Relevant hits were consumers `CommonFieldSemilinearInduction` and
  `FiniteClosedSetRationalLifts`; the former was opened and states the subsequent
  scheme induction, not this product-group construction or kernel-image equality.
- Exact proposed declaration-name search
  `common_normal_compatible_groups` in the same source roots and name index:
  no matches.

Validation: the prescribed scompile.py compiled the delivered file in sandbox
and library module modes, each in 1.3 seconds, with no diagnostics. Only the
named theorem is postponed. No statement dispute, dependency fault, extra node,
or statement correction was needed.

## Second reading by Q25

This is the worker's own second pass; the dispatcher prohibits starting another
agent and the maintainer supplies the independent review. I reopened the node
and the complete Lean file and checked each row of the correspondence table.
The key checks were that Gamma is defined by an iff for ALL ambient pairs,
that r equals the actual ith coordinate on EVERY element, that the kernel image
includes the subgroup inclusion before projection, and that the fixed field is
of the projection's actual range. The group is literally the specified product,
not an arbitrary finite group. The normality and pure-inseparability interfaces
include inseparable cases. No discrepancy was found and no revision was needed.
