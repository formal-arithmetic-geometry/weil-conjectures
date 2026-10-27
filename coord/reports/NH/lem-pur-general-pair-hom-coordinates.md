## Worker report

The new module `Sheaf.Paper.GeneralPairHomCoordinates` states
`WeilConjectures.GeneralAlgebraicallyClosedCoefficients.pairHomCoordinates`, with its
whole proof `sorry`. It collects precisely the complete interface of
`lem-pur-general-pair-hom-coordinates` on the existing intrinsic constructions.
It defines no new category, transport, colimit, coordinate equivalence or group law.
The existing `homCoordinates_existsUnique` alone covers only the coordinate-equivalence
clause: it does not state the node's full conjunction. In particular the existing
same-stage addition and zero facts are private, and `zero_exists` asserts existence
of a zero object rather than the literal bottom-field pair conclusion for any stage
zero object. This delivery exposes the full node as one statement, reusing all objects.

Hypotheses and objects:

- `l : ℕ` with `[Fact l.Prime]` is exactly the specified prime.
- `Ω : Type v`, `[Field Ω]`, `[Algebra (Padic l) Ω]`, and
  `[IsAlgClosure (Padic l) Ω]` fix an arbitrary algebraic closure of the Mathlib
  l-adic field. `Y : AlgebraicGeometry.Scheme.{u}` is arbitrary, with `u` and `v`
  independent. There is no finite-field datum, structure map, noetherianity,
  characteristic exclusion, or idempotent-completeness hypothesis.
- `Padic.FiniteCoefficientFields l Ω` is the recorded finite-intermediate-field
  index. `Stage l Ω Y E` is the recorded intrinsic rational category with its
  small coefficient model, as defined in
  `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`. `stageSystem l Ω Y`
  uses exactly the specified scalar transitions and normalized associators;
  its integer-shift comparisons are those of `stageTransitionCommShift`.
  No shift assertion is added to this Hom-only node.
- `Pair l Ω Y` abbreviates `(stageSystem l Ω Y).PairCategory`, with actual
  objects `(E,K)`, the upstream quotient of representatives, and its existing
  composition and identities. The node does not assume an `ExactStagePairData`,
  which would already assume the additivity and zero structures being asserted.
  That dependency's underlying `StageSystem` and quotient construction are reused.
- `Common A B` is precisely `{L // A.stage ≤ L ∧ B.stage ≤ L}`; `StageHom A B L`
  is precisely the Hom between the two specified scalar images at `L`.
  `transportHom` has underlying `transport`, defined as the source-associator
  inverse, scalar image of the arrow, then target-associator hom. In Lean's
  left-to-right `≫` convention this is the node's displayed formula.
  `ColimitHom A B` is `AddCommGroup.DirectLimit (StageHom A B) (transportHom A B)`;
  `colimitOf` is its canonical homomorphism evaluated on the representative.

Each conclusion, in the order of the conjunction:

1. `∀ A B, DirectedSystem (StageHom A B) (fun {L M} h ↦ transportHom A B L M h)`
   states both reflexive identity and iterated transport laws. The maps are
   already bundled additive homomorphisms, hence this is a directed system of
   abelian groups with the specified formula, rather than arbitrary functions.
2. `∀ A B, ∃! e : (A ⟶ B) ≃ ColimitHom A B, ...` states uniqueness among set
   equivalences with `e (StageSystem.PairCategory.mkHom L hA hB f) =
   colimitOf A B L hA hB f` for every representative. It refers to the actual
   quotient Hom, not an unspecified equivalent category.
3. The same-stage sum equality is `ofHom ... f + ofHom ... g =
   ofHom ... (f + g)` for arbitrary `A,B,L,hA,hB,f,g`.
4. The same-stage zero equality is `ofHom ... (0 : StageHom ...) = 0`.
   Here `ofHom` is the existing abbreviation for `PairCategory.mkHom`.
   The pair Hom group used by these operations is the existing `homAddCommGroup`,
   defined literally as `(homCoordinates A B).addCommGroup`. The existing
   `preadditive` uses this exact `homGroup`; it does not introduce another law.
   The chosen `homCoordinates` is selected from the unique normalized
   equivalence in clause 2, so these are exactly the requested transferred groups.
5. `(f + f') ≫ g = f ≫ g + f' ≫ g` is additivity of composition in the first arrow.
6. `f ≫ (g + g') = f ≫ g + f ≫ g'` is additivity in the second arrow.
7. `∀ E, (inclusion E : Stage ... E ⥤ Pair ...).Additive` uses the specified
   inclusion `(stageSystem ...).ι E`, with its existing reflexive-scalar arrow
   formula, and the same transferred groups.
8. For every `Z : Stage ... (Padic.finiteCoefficientBase l Ω)`, the implication
   `IsZero Z → IsZero (⟨Padic.finiteCoefficientBase l Ω, Z⟩ : Pair l Ω Y)`
   states the zero-object conclusion for the literal bottom-stage pair, rather
   than merely asserting some zero object exists.
9. `∀ A B f, ∃ L hA hB g, f = ofHom A B L hA hB g` supplies a finite
   representative of every morphism.
10. The final biconditional identifies equality of representatives at any two
    common stages with the existence of `N : Common A B` and `hL,hM` such that
    `transport A B L N hL f = transport A B M N hM g`. This uses the specified
    associator-conjugated transports throughout, including repeated stages.

Dependency declarations read and used:

- Mathlib `Padic` (`Mathlib.NumberTheory.Padics.PadicNumbers`) and `IsAlgClosure`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`), the recorded Mathlib matches.
- `Sheaf.NumberTheory.Padics.FiniteCoefficientFields`: `Padic.FiniteCoefficientFields`,
  `finiteCoefficientCompositum`, `finiteCoefficientBase`, and
  `finiteCoefficientFields_properties`, including their signatures and docstrings.
- `Sheaf.Paper.SfRationalizationKaroubi`: `sfRationalConstructibleCategory`,
  `sfRationalConstructibleZero` and the shift/triangulation interface, used through
  the recorded intrinsic `Stage` definitions. No rationalization is redefined.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages`: `Stage`, `stageCategory`,
  `stagePreadditive`, `stageZero`, `stageSystem_existsUnique`, `stageSystem`,
  `stageTransition`, `stageTransitionCommShift`, `stageTransition_additive`,
  `associator`, and `unitor`. Their small models preserve the independent universes.
- `WeilConjectures.CategoryTheory.StageSystem.Basic` (also publicly reached through
  the dependency module `Sheaf.CategoryTheory.ExactStagePairData`): `StageSystem`,
  `tr`, `PairCategory`, `PairCategory.Rep`, `PairCategory.mkHom`, `ι`, and
  `PairCategory.mkHom_eq_mkHom_iff'`. The recorded `ExactStagePairData` packages
  supplied extra structures; this node only needs its underlying stage construction.
- Mathlib `AddCommGroup.DirectLimit` and `.of`
  (`Mathlib.Algebra.Colimit.Module`), and `DirectedSystem`
  (`Mathlib.Order.DirectedInverseSystem`), through the existing colimit construction.
- `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`: `Pair`, `Common`, `StageHom`,
  `transport`, `transportHom`, `transportSystem`, `ColimitHom`, `colimitOf`,
  `homCoordinates_existsUnique`, `homCoordinates`, `homAddCommGroup`, `ofHom`,
  `preadditive`, `inclusion`, `composition_bilinear`, `inclusion_additive`,
  `representatives`, and `zero_exists`. The signatures, definitions and proof
  docstrings around each were read. The private `mkHom_add`/`mkHom_zero` are not
  referenced by name in the new statement.

Edge cases checked before writing:

- `E=F`, `L=M`, and completely reflexive chains: no strict equality
  `T_EE = 𝟭` is imposed. The existing normalized unitor makes reflexive transport
  injective, so its cocycle idempotence gives identity.
- Empty common index cannot occur: the compositum of the two finite fields belongs
  to it. Composita also give directedness; no extraneous nonemptiness hypothesis.
- Zero objects and zero arrows: sums and zero use the transferred group, and
  the bottom-pair conclusion is asserted for every stage zero object. This also
  covers a trivial stage/category and the empty scheme.
- Arbitrary schemes, including the empty scheme and schemes with no selected
  finite-field structure, remain allowed. The coefficient universe `v` can be
  larger or smaller than the scheme universe `u`; no equality or inequality is added.
- There is no shift-zero or integer-sign exclusion: the fixed stage comparisons
  come from the normalized-stage dependency, while this statement imposes no new
  shift construction or extra compatibility hypothesis.

Searches made on 2026-10-27:

- `msearch.py ... leanfinder "A directed stage pair category has unique representative
  normalized Hom direct limit coordinates, transferred abelian groups, bilinear
  composition, additive inclusions and a bottom zero object"`: eight generic hits,
  including `AddCommGroup.DirectLimit.directedSystem`, `Module.DirectLimit.exists_of₂`,
  and `AddCommGroup.DirectLimit.map`; no complete intrinsic interface.
- `msearch.py ... leansearch "The quotient by eventual equality of a directed system
  of abelian groups is its direct limit, and each element is represented at a stage"`:
  eight hits including `AddCommGroup.DirectLimit`, `DirectLimit.exists_eq_mk`,
  `Module.DirectLimit` and `ModuleCat.directLimitCocone`; generic constructions only.
- `msearch.py ... loogle "Module.DirectLimit.linearEquiv, AddCommGroup.DirectLimit"`:
  zero hits. Retried the valid single-name query `Module.DirectLimit.linearEquiv`:
  three hits (`linearEquiv`, `linearEquiv_of`, `linearEquiv_symm_mk`); these give
  the generic algebraic/set-colimit bridge, not the full concrete conclusion.
- `msearch.py ... grep "linearEquiv|def DirectLimit|theorem exists_of|of_f"
  Algebra/Colimit/Module.lean`: five hits, including `DirectLimit.moduleCon`,
  `DirectLimit`, `of_f`, and `exists_of`. Directly read `AddCommGroup.DirectLimit`,
  its canonical maps, and `DirectedSystem` in Mathlib.
- `msearch.py ... grep "homCoordinates_existsUnique|HomCoordinates" Sheaf`: zero
  hits; this Mathlib-directory query is not evidence about the project. The actual
  project search below finds the existing concrete constructions and is used instead.
- `rg -n "AddCommGroup.DirectLimit|Module.DirectLimit|homCoordinates" lean/Sheaf
  lean/WeilConjectures` and `rg -n "homCoordinates_existsUnique|homCoordinates|general.*pair"`
  in both trees found the intrinsic general module plus the older finite-field
  and ordinary PBC constructions. The ordinary and finite-field constructions
  have different categories/hypotheses; all intrinsic constructions are reused.
- `rg` for `PairCategory`, `StageSystem`, `StageHom`, `transportHom`, `zero`,
  `mkHom_add` and `mkHom_zero` read the exact general, normalized-stage, rationalization
  and StageSystem sources. The individual core theorem, composition, additive
  inclusion and representation assertions already exist, but no single existing
  declaration states the complete node. The private same-stage formulas and
  the stronger literal-bottom-pair clause account for the additional public statement.
- `grep -rn "lem-pur-general-pair-hom-coordinates" lean/WeilConjectures`: no hit.

No statement correction, disputed statement, new notion, or unusable dependency
was found. Only the item's `lean` record is changed. The docstring gives every
proof step of the node, including the reflexive-transport faithfulness argument.

## Second reading by NH

The dispatcher explicitly prohibits starting other agents, and the delivery is
reviewed independently by the maintainer. This section records the worker's own
second pass; it does not claim an independent reading by another agent.

Re-read the node, the new signature and the definitions it uses. The ten conclusion
blocks match the directed-system assertion, normalized unique equivalence, sum,
zero, both bilinearities, additive inclusions, literal bottom zero pair, finite
representatives and eventual equality, in that order. Checked that the normalization
quantifies over all representatives and uniqueness is among set equivalences;
that `StageHom`, `transportHom`, `ColimitHom`, `ofHom` and `Pair` are the existing
intrinsic objects; that `+` and `0` use `homAddCommGroup` via the existing
preadditive instance; that the bottom-pair clause is universally quantified over
stage zero objects; and that `u` and `v` remain independent. No mismatch was found
and no mathematical correction was made.

## Import direction

The already published owning module `Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients`
contains the fixed constructions and is imported here. Its node
`def-weil-algebraically-closed-coefficients` now cites this item as a proof dependency.
A future automatic back-import of this new module into that owning module would close
a Lean import cycle and must be omitted under stages/2-statements.md §3(7). This
delivery does not edit the owning module or alter any of its definitions.

## Validation

Remote single-file compile through `scompile.py` passed with exit 0 and no diagnostics.
The wrapper compiled sandbox `Sheaf.Stage2.Sandbox0` in 4.5 s and the delivered
library module `Sheaf.Paper.GeneralPairHomCoordinates` in 2.3 s, both within 60 s.
Only dependency overlays were prepared; no global build was run.
`deliver2.py NH lem-pur-general-pair-hom-coordinates --no-push` passed server
preflight and compilation, printing `OK (dry run)` for commit `873b290d950`.
The staged paths were exactly this report, the item node and the Lean module.
The final report update is checked again before the prescribed delivery push.
