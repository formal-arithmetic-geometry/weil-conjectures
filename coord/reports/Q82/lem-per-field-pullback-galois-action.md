## Worker report

Q82 states `lem-per-field-pullback-galois-action` in
`Sheaf.AlgebraicGeometry.FieldPullbackGaloisAction`. The only postponed theorem is
`AlgebraicGeometry.Scheme.fieldPullback_galoisAction`; its proof is `sorry`, with
the five-step accepted proof in its docstring. Two supporting definitions have
real data: `Rep.restrictDiscrete` lifts Mathlib's `Rep.resFunctor` to the recorded
full subcategories, and `Scheme.fieldStalkActionCompatible` packages exactly the
abelian lift-change formula of the recorded stalk equivalence. They belong to
the restriction and canonical-equivalence clauses of this node, and are listed
in `lean.declarations`. No new independent notion, node, dependency repair, or
statement correction is needed. Only the item's `lean` field changes.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

* Fields K contained in L: `(K L : Type u) [Field K] [Field L] [Algebra K L]`.
  The spectrum map is always the actual
  `Spec.map (CommRingCat.ofHom (algebraMap K L))`, never a supplied arbitrary map.
* Compatible separable closures: fields `Ks`, `Ls`, the algebra structures
  `K → Ks`, `L → Ls`, `Ks → Ls`, `K → Ls`, together with
  `[IsSepClosure K Ks]`, `[IsSepClosure L Ls]`,
  `[IsScalarTower K L Ls]`, and `[IsScalarTower K Ks Ls]`.
* Omega containing Ls and algebraically closed: `[Field Ω] [IsAlgClosed Ω]`
  and `[Algebra Ls Ω]`. The named algebra structures from K, L, and Ks into
  Omega have the compatibility instances `IsScalarTower K Ls Ω`,
  `IsScalarTower L Ls Ω`, and `IsScalarTower Ks Ls Ω`.
  These are commuting diagrams expressing the given inclusions, rather than
  algebraicity or separability assumptions on L/K or Omega/Ls.
* Absolute Galois groups and Krull topologies: the actual `Gal(Ks/K)` and
  `Gal(Ls/L)` with the imported Krull topology instances. The supplied
  monoid homomorphism `r` is specified by `hres`: its action commutes with
  the embedding of Ks in Ls, so it is literally restriction. Injectivity of
  this embedding makes that characterization unique. There is no continuity,
  surjectivity, or algebraicity hypothesis. The existential `h` in the
  conclusion establishes that restriction gives discrete continuous modules.
* The geometric points are the actual `Spec.map (algebraMap L Ω)` and its
  composite with `Spec.map (algebraMap K L)`. In particular p_K is literally
  p_L followed by u, as requested. Compatibility of the towers identifies
  that composite with `Spec.map (algebraMap K Ω)`.
* `EK` and `EL` have exactly the sheaf and discrete-module categories of
  `lem-exc-abelian-sheaves-gmodules`. The accompanying natural additive
  comparisons `iK`, `iL` identify their underlying groups with the geometric
  stalks. `hK` and `hL` specify their canonical action: for every extension
  of a separable-closure automorphism to Omega, changing the pointed lift
  gives its action on a germ. These are the witnesses and normalization
  returned by the dependency theorem, rather than additional conditions on
  a field inclusion or a sheaf. Quantifying over these normalized witnesses
  makes the result usable independently of choices of quasi-inverse or
  presentation of the equivalences; it does not choose a second equivalence.
* The asserted natural additive isomorphism is `e`, with type
  `Etale.upperStar ... u ⋙ EL.functor ≅ EK.functor ⋙ Rep.restrictDiscrete r h`.
  Components are morphisms in the full subcategory of integral representations,
  hence additive equivariant isomorphisms. Naturality is part of `NatIso`.
* The restriction clause uses `ObjectProperty.lift` of the existing
  `Rep.resFunctor r`. On objects it is `M.ρ.comp r` on the same module;
  on morphisms it is `Rep.resMap`, retaining the underlying linear map.
  The proof argument `h` supplies only open stabilizers, and is itself asserted
  to exist by the theorem. No representation is chosen from existence.
* The first conjunct quantifies over every F and every element m of its
  pulled-back module. It states
  `iK(e(m)) = upperStarCompSheafFiberIso(iL(m))`.
  Thus the underlying isomorphism is the actual canonical stalk-pullback
  comparison, not an arbitrary equivariant additive bijection.
* Global sections are evaluated at any terminal object `T` of the K-site;
  its base change `u.Etale.obj T` is terminal over L. The chosen lift x and
  its canonical base-change lift are used in the actual terminal germ maps.
  This is the standard terminal-object representation of global sections.
* The additive equivalence `a` identifies the K global sections with the
  actual Mathlib `Representation.invariants` of `EK(F)`, and its first
  normalization equation identifies its underlying map with `iK.inv` of
  the terminal germ. The additive equivalence `b` identifies the L global
  sections with `Representation.invariants (EK(F).ρ.comp r)`; its second
  normalization equation identifies its underlying map with the terminal
  germ followed by `iL.inv` and the very same `e`.
* The last equation applies b to the unit of the recorded
  `Etale.upperStarLowerStarAdjunction` at T. Its underlying value equals
  that of a on the original section. Therefore, under the specified
  canonical identifications, the global pullback is exactly the inclusion
  `m ↦ m` between the two invariant subgroups. The identifications are
  determined by their normalization equations and hence have the usual
  naturality in F. The conclusion is an inclusion, not a claimed bijection
  between the two invariant subgroups.

Dependency declarations read and used:

* `Mathlib.Algebra.Algebra.Defs`: `Algebra`, specialized to fields.
* `Mathlib.FieldTheory.IsSepClosed`: `IsSepClosed`, `IsSepClosure`.
* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
* `Mathlib.FieldTheory.IsAlgClosed.Basic`: `IsAlgClosed`; the geometric
  point is inline as in the node's record. `Scheme.SpecToEquivOfField` in
  `Mathlib.AlgebraicGeometry.ResidueField` was also read; no residue-field
  presentation or duplicate geometric-point definition is needed here.
* `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`:
  `Scheme.abelianSheaves_equiv_discreteGModules`. Its full type and
  docstring were read. The binder types and action predicate are exactly
  its abelian witnesses, specialized to coefficient universe u+1 and with
  the K-point expressed as the literal composite p_L followed by u.
* `WeilConjectures.RepresentationTheory.DiscreteContinuousRep`:
  `Rep.DiscreteContinuousRep`, the recorded full subcategory with open
  stabilizers, used unchanged.
* `WeilConjectures.AlgebraicGeometry.EtaleSheaves` and its imported
  `CategoryTheory.Sheaf`: abelian sheaves are
  `Sheaf S.smallEtaleTopology AddCommGrpCat.{u+1}`. No constructibility,
  torsion or finiteness property is required.
* `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`:
  `Etale.upperStar` and `Etale.upperStarLowerStarAdjunction`, imported
  through the public Stalk module. The latter supplies the actual unit.
* `Sheaf.AlgebraicGeometry.PointedEtaleStalk`: `pointedEtaleStalk`,
  `pointedEtaleStalkDiagram`, `pointedEtaleGerm` were read. For abelian
  groups this is definitionally the same colimit as the `Point.sheafFiber`
  in the equivalence's recorded interface, used here with
  `pointSmallEtale` and `Point.toPresheafFiber`.
* `Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure`: `AlgebraicClosure`
  and the general `IsAlgClosure` interface were read. Only `IsAlgClosed Ω`
  is used: the node does not make Omega an algebraic closure of K or L.
* Further existing maps: `Etale.upperStarCompSheafFiberIso` in
  `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`,
  `pointSmallEtaleFiberEtaleIso`, Mathlib's `Rep.resFunctor`,
  `ObjectProperty.lift`, and `Representation.invariants`.

Every recorded proof-dependency module is imported, privately when it is needed
only for the future proof: `InverseImageStalkGerm`,
`GaloisAutomorphismExtension`, `AbelianSheavesGModulesAction`, and the two
`EtaleGlobalSectionsGalois{Injective,Image}` modules. The equivalence and the
discrete-module/geometric-stalk definitions are already public statement
dependencies. `lem-per-galois-restriction-image` currently has no Lean record,
so there is no corresponding module to import. The statement does not assume
its conclusion: well-definedness of discrete restriction is included in the
existential conclusion. Its future continuity proof is step 1 of the docstring.

Edge cases checked before and during writing:

* K = L, compatible equal closures, r = identity: the comparison is the
  ordinary identity-pullback stalk comparison; the invariant inclusion is
  the identity. No strict inclusion is imposed.
* R contained in C, with the larger Galois group trivial: the right invariant
  group can be larger; the theorem only says the global map is the inclusion.
* Purely inseparable L/K: there is no separability hypothesis on that
  extension, and the restricted action is still the correct one.
* Transcendental L/K and Omega larger than an algebraic closure: neither
  algebraicity assumption is present. The canonical-action formula uses every
  extending automorphism and the accepted proof extends automorphisms to
  arbitrary algebraically closed Omega.
* The zero sheaf/module: both additive equivalences and the last equation
  reduce to their unique zero-group versions; no nonzero stalk is assumed.
* Arbitrary sheaves, infinite groups and non-surjective r: no finite,
  constructible, lisse or surjective assumption appears. The stabilizer
  property is proved in the conclusion rather than assumed of the fields.
* Size: the standard project convention is schemes/fields in universe u
  and abelian sheaves in u+1. All universes are explicitly declared, and
  the generic restriction helper independently binds group and module
  universes. No extra equality of different site universes is imposed.

Searches actually run (the msearch log is `searches.jsonl` in the sandbox):

* LeanFinder, “Pullback of an abelian etale sheaf along a field extension is
  restriction of its absolute Galois action on the geometric stalk”: eight
  hits, including `finGaloisGroupMap`, `InfiniteGalois.proj`, and module-sheaf
  pullback facts; none states this theorem.
* LeanFinder, “Pullback of abelian etale sheaves along a field extension
  corresponds to restriction of Galois action”: eight hits including
  `galRestrict`, `galRestrictHom`, `finGaloisGroupMap`, and module-sheaf
  pullback facts; no exact theorem.
* Loogle, `Rep.res, Rep.invariants, Representation.invariants`: unknown
  identifier `Rep.invariants`; this was not treated as a negative result
  for the actual invariants definition.
* Loogle, `Rep.resFunctor`: twelve hits, including the existing restriction
  functor and its additive instance. That functor is reused, with only the
  lift to the existing open-stabilizer full subcategories supplied here.
* msearch grep, `def.*(res|restrict)|invariants` in RepresentationTheory:
  25 reported hits, including the invariants module. Direct source reading
  found and reused `Rep.resFunctor` and `Representation.invariants`.
* msearch grep, `sheafFiber.*(resFunctor|restrict)|pullback.*Galois`:
  two unrelated hits (ideal-sheaf Galois connection and point API comment).
* Direct rg of `lean/WeilConjectures` and `lean/Sheaf` for
  `pullback.*[Gg]alois|[Gg]alois.*pullback` and the discrete/restriction
  patterns found other geometric Frobenius, finite-etale, pro-etale and
  finite coefficient statements, not the small-etale field-stalk statement.
* Direct grep of the item's blueprint id in `lean/WeilConjectures` had no
  hits. Direct searches for all three new full-name suffixes in Mathlib,
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
  found no collisions.

Source checks used the local Stacks text at the recorded labels:
`lemma-stalk-pullback`, `section-galois-action-stalks`,
`lemma-equivalence-abelian-sheaves-point`, and `lemma-global-sections-point`.
They give exactly the comparison, action normalization, abelian equivalence,
and canonical invariant identification used above. No source discrepancy or
STATEMENT-DISPUTED issue was found.

Validation: `scompile.py Q82 lem-per-field-pullback-galois-action` compiled
the delivered module successfully in both sandbox and library module modes,
with no errors or warnings. The invariant subgroups explicitly retain the
representation's stored integral module structures to avoid the elaborator
selecting a second, definitionally different, integral module instance.

## Second reading by Q82

I reopened the node and the complete module after compilation and checked
each binder and conclusion against the source. This is a second pass by the
same worker, under the explicit instruction not to start other agents; the
maintainer's independent delivery review remains separate.

The restriction helper has actual functor data and introduces no new action;
its open-stabilizer proof is existentially established by the main theorem,
not an added hypothesis. The action predicate unfolds to the dependency's
canonical formula, with the same direction of precomposition by Spec(tau).
The K-point is the composite p_L followed by u, so the canonical stalk map
has exactly the required target without a silently changed geometric point.
Both canonical equivalences have their normalization included, so no arbitrary
equivalence can satisfy the binders by changing the Galois action.

The first conjunct fixes the underlying map, and the last three equations fix
both invariant identifications and the actual pullback of global sections.
The use of any terminal T is equivalent to evaluating at Spec K, and its
base change is terminal over L. The two invariant groups are genuinely those
of EK(F) and its restricted representation on the same underlying group.
No surjectivity of r, algebraicity of L/K or Omega, coefficient finiteness,
or sheaf constructibility was introduced. There are no lets, local notation,
local instances, auto-bound variables, hollow definitions, or extra axioms.
The two initial elaboration repairs were replacing a plain fixed-element
subtype (which had no additive instance) by Mathlib's invariants submodule,
then specifying the representation's stored module instance explicitly.
Neither repair changed the mathematical statement. The node's statement and
accepted split are unchanged.
