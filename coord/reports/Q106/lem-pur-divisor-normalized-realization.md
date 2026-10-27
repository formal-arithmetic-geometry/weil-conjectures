## Worker report

This delivery states the supported Kummer realization for an arbitrary framed line bundle. The main theorem is `WeilConjectures.PurityFiniteSetting.divisor_normalized_realization`; the isomorphism, additivity, etale-pullback and enlargement clauses are the four `divisorRealization_*` companion theorems. All theorem proofs are `sorry` with source and proof-plan docstrings. Definitions use actual maps or selection from an explicitly unique characterization.

Hypotheses and clauses, in order:

- The finite datum is `P : PurityFiniteSetting.{u}`. Its existing `Coefficient`, positive `level`, `diagonalExponent`, `diagonalExponent_annihilates` and `diagonalExponent_isUnit a` supply exactly A, n>=1, m=ell^n, mA=0 and invertibility on T. There is no ramification-index divisibility hypothesis.
- The structural arrow `a : T → Spec k`, with `LocallyOfFiniteType a`, `QuasiCompact a` and `IsSeparated a`, says separated finite type. Explicit a is used because the recorded Kummer/root-pullback APIs take that arrow. Scheme universe u, site object universe u+1, coefficient universe u+1 and Ext universe u+1 are explicit; `autoImplicit` is false.
- `i : Z → T` with `IsClosedImmersion i` is arbitrary closed support. `i.openComplement` is W and its actual inclusion is used as the etale object of every frame. Neither a Cartier ideal nor a regularity assumption occurs.
- `L : T.Modules` with `Scheme.Modules.IsInvertible L` is the recorded notion of invertible module. `divisorFrameTorsor L` abbreviates the existing `Scheme.Modules.etaleIsoTorsor`, using the recorded invertibility bridge. A section `s` of this Isom torsor on W is literally a frame of L on W; no global section is selected.
- `DivisorRelativeExtension i L s β` quantifies an actual short exact abelian sheaf extension E, its two arrows, and an equivariant torsor map f. It records f(g+p)=f(p)+a(g), image equal to the restriction of the supported integer one, f(s)=0, and β equal to the extension's Yoneda class. `divisorRelativeExtension_existsUnique` gives the stated uniqueness; `divisorRelativeExtension` chooses precisely that uniquely determined class. This is the Ext normalization, without identifying it with the raw cone cocycle.
- `divisorIntegralSplice a i β` composes β with the extension class of `T.kummerSequence_shortExact m ...`, then with `Etale.ordinaryFiniteRootMap`. This is the positive Yoneda composite and the existing root tensor unit. Gm remains an abelian sheaf throughout.
- The module class has exactly type `Ext (i_* P.constantEtale Z) (P.frameTwistEtale T 1) 2`. The frame twist is the existing finite root tensor presentation of A(1). `divisorAbelianRealization i b` is exact forgetting followed by precomposition with `Etale.supportedIntegralGenerator`. The first equation of the main theorem is exactly the requested integral realization equation. `divisorScalarRealization_existsUnique` and its choice give b_A as a named construction. The generic `DivisorUniqueRealization` is only the predicate `∃! b, f b=x`.
- `DivisorProGroup i` reuses the actual support-hypercohomology functor, evaluated at the bounded-below degree-zero coefficient object `divisorProCoefficient`. `DivisorProRealizes` requires every cocycle-normalized `SupportHomPair.Identification` to send the class to the existing `functorialCupCompare` of b_A. Thus this is actual supported cohomology, not a fresh Hom-based definition of cohomology. The inverse-image root tensor presentation is exactly the sigma-rho prescription of `frameTwist`/`frameKummer`. Its normalization is evaluation at one on injective representatives, so no arbitrary comparison or choice of root is assumed.
- `divisorRealization_iso` takes an actual section-preserving `Sheaf.Torsor.Iso` and states equality of β and both realized classes. This covers isomorphisms of the framed pair through its actual frame torsor.
- `divisorRealization_additive` states preservation of zero and addition for every integral extension β, not merely those supplied by a globally trivial line.
- `divisorRealization_pullback` uses an arbitrary etale v and the existing `ChosenCartesianSquare`. It uses the actual `functorialCupPullback` on both sites. `divisorPulledFrame` transports the upstream pulled frame to `Scheme.Modules.tensorPullback v` via the canonical isomorphism fixed by `exists_tensorPullbackAdjunction`. Its parameter hW only identifies the complement of the inverse-image support with v inverse W, which every Cartesian closed pair satisfies. No finite-type or separatedness condition is imposed on v or its source by the realization helpers.
- `divisorRealization_enlarge` uses g with g≫i'=i and the actual `functorialCupChangeSupport`. `divisorRestrictedFrame` restricts s by the actual etale sheaf map to the smaller complementary open. The displayed hW is precisely the complement inclusion forced by this support factorization.
- `divisorOrdinaryKummer` is the positive `T.kummerδ₁` of `Sheaf.Torsor.classH1` of the frame torsor, followed by the identical `ordinaryFiniteRootMap`. The second equation of the main theorem says forgetting support has exactly this abelian realization. Its last equation says the pro-etale forget-support image is the identical ordinary site comparison of this etale image. Together these give the positive ordinary Kummer image with exactly the same roots/site maps.

Dependency interfaces read and reused:

- `Sheaf.Paper.PurityFiniteSetting`: `WeilConjectures.PurityFiniteSetting`, `constantEtale`, `constant`, `diagonalExponent` and its annihilation/invertibility properties.
- Mathlib: `AlgebraicGeometry.IsClosedImmersion`, `IsOpenImmersion`, ordinary `CategoryTheory.Abelian.Ext`, its `comp`, `mk₀`, `mapExactFunctor` and `hom`.
- `WeilConjectures.AlgebraicGeometry.Modules.Invertible`: `Scheme.Modules.IsInvertible` and its bridge to `SheafOfModules.IsInvertible`.
- `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`: the recorded frame-torsor/Picard interface, including `Scheme.Modules.etaleIsoTorsor`; `GmPicardPullback`: `Scheme.etaleIsoTorsorPullback`.
- `Sheaf.CategoryTheory.Sites.TorsorWithSection`: `Sheaf.Torsor.WithSection`, `IsIsomorphic`; the concrete torsor and specified section are kept separately in the signatures. `RelativeTorsorExtension`: `Sheaf.Torsor.relative_extension_existsUnique`.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `Scheme.kummerSequence_shortExact`, `kummerδ₁`.
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`: the ordinary etale and pro-etale module categories and exact scalar-forgetting infrastructure.
- `Sheaf.AlgebraicGeometry.OrdinaryFiniteP1Kummer`: `Etale.ordinaryFiniteRootMap`, `ordinaryFiniteClass`, and the integral/module realization conventions.
- `Sheaf.AlgebraicGeometry.OrdinarySupportedKummerBoundary`: `supportedIntegralConstant`, `supportedIntegralUnit`, `supportedIntegralOne`, `supportedIntegralGenerator`. Its Cartier-specific predicate is not reused for arbitrary closed support.
- `Sheaf.AlgebraicGeometry.ClosedSupportHom`: `Etale.closedSupportHom`; `RelativeTorsorCohomology`: `Etale.relative_torsor_cohomology`; `SupportCohomology`: `Sheaf.supportHypercohomologyFunctor`.
- `Sheaf.Paper.PurityFrameKummer`: `frameTwistEtale`, `frameTwist`, `frameKummer`; these are the existing root/scalar/site maps of `def-pur-frame-class`.
- `Sheaf.Paper.SupportedHomPullback`: `SupportHomPair.Identification`, `proEtaleSupportHomPair`, `supportedHom_pullback`. The identification includes the evaluation-at-one normalization, not merely existence of an isomorphism.
- `Sheaf.Paper.SupportedCupFunctoriality`: `FunctorialCupH`, `functorialCupCompare`, `functorialCupForget`, `functorialCupOrdinaryCompare`, `functorialCupPullback`, `functorialCupChangeSupport`.
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`: `Scheme.Modules.exists_tensorPullbackAdjunction`; `Adjunction.leftAdjointUniq` gives the canonical tensor/Mathlib pullback comparison used only to transport the upstream frame construction.

Edge cases checked mathematically: Z empty makes supported Ext and cohomology zero; W empty imposes the unique empty frame and recovers the ordinary torsor extension; W=T forces the supported class to vanish. Empty T is allowed. A trivial line with a nonconstant complementary frame remains meaningful and is not silently assigned zero. Non-Cartier and nonreduced closed subschemes are allowed. Level zero is excluded by the existing datum, while every positive level, including ramified levels, is allowed. Identity etale pullback, arbitrary etale pullback, equality of supports and proper enlargement all use the same canonical operations. No extension of s to T, purity isomorphism, flatness of A over Z/m, or Z/m-module structure on Gm is assumed.

Searches: prescribed msearch `leansearch` query “The supported Kummer class of a framed line bundle is realized by the integral Yoneda extension and unique finite coefficient lift” returned eight unrelated generic Yoneda/Kummer-field/cohomology hits. `leanfinder` query “Relative torsor integral extension with a specified zero complementary frame and normalized pro etale supported realization” returned standard-etale presentations and normalization-diagram hits. `loogle CategoryTheory.Abelian.Ext` found the generic Ext API, reused here. Prescribed Mathlib grep `framedRealization|divisorScalar|relativeTorsor` returned zero hits. Project rg of `divisorRelativeExtension|divisorIntegralSplice|DivisorProRealizes|framed.*realization` and the item-id grep in WeilConjectures returned no existing exact declaration. `blueprint_refs.py search framed` returned zero blueprint nodes; DAG id searches found no existing `def-pur-framed-*` node. Searches and their raw wrapper results are recorded in each new node. Existing generic torsor extension, scalar/root and normalized support notions are reused; only the specialized composite/uniquely characterized data are newly named.

No statement correction or disputed statement is asserted. The node's original statement and proof are preserved. Its statement dependencies gain the newly named canonical constructions and landed frame/integral interfaces; the normalized support interfaces are cited by the new definition nodes.

## New nodes

`def-pur-framed-integral-extension` defines the precise integral extension characterization and its unique value for a framed invertible line on any closed pair, using the existing relative-torsor theorem. Source: Stacks 03AJ and the blueprint framed-line construction. The generic extension theorem does not itself select this specialization on the canonical open-closed integer sequence.

`def-pur-framed-scalar-maps` defines the positive roots-coefficient Yoneda splice, using the actual Kummer short exact sequence and root tensor unit. Source: Stacks 03PL and the blueprint realization equation. Generic Ext composition is reused; the fixed composite was absent.

`def-pur-framed-abelian-realization` defines exact forgetting precomposed with the supported integral generator. Source: the integral derived adjunction and Stacks 03FD. It also names the elementary unique-realization predicate to keep the specialized signatures small.

`def-pur-framed-scalar-realization` defines the unique finite module class determined by that exact abelian-realization equation, for every integral extension. Source: the integral derived-unit bijection and the blueprint scalar clause. This is a unique characterization, not choice from unconstrained existence.

`def-pur-framed-pro-realization` defines the actual right-derived supported class by every normalized supported-Hom identification and canonical site comparison. Source: Stacks 0A45/099W and the same sigma-rho frame coefficient convention. No second definition of support cohomology is introduced.

`def-pur-framed-transport` names the canonical pulled and restricted frames, the tensor-pullback transport of the upstream frame map, and the positive ordinary Kummer image used by the naturality/forget-support statements. Source: Stacks 03AJ, 03PL and 0096. It uses the canonical adjunction comparison; no arbitrary transport is supplied as a hypothesis.

For all new nodes the three prescribed search kinds and project/DAG searches found no exact definition of these specialized data; the generic components found are imported and used. Separate modules keep each server compile within its prescribed per-file budget.

For compilation, the five longer clauses are named as Prop-valued definitions in `def-pur-framed-realization-iso`, `def-pur-framed-realization-additive`, `def-pur-framed-realization-pullback`, `def-pur-framed-realization-enlarge` and `def-pur-framed-realization-property`. Each definition spells out the corresponding quantifiers and equations described above. The main module's five theorems assert exactly these predicates; their full source/proof docstrings remain there. These predicates introduce no additional hypothesis or axiom. They are separate modules because repeatedly checking all concrete derived-category expressions in a single file exceeded the fixed compile budget. Searches are the same framed-realization searches recorded above; no such specialized predicates already exist.

`def-pur-framed-pro-predicate` separately owns the actual support group abbreviation, degree-zero coefficient, normalized Hom wrapper, and realization predicate. `def-pur-framed-pro-realization` owns just existence/uniqueness and selection of the unique class. This separation preserves exactly the same canonical comparison equation.

`def-pur-framed-forget-support` names the three canonical forget-support composites already described in the clause mapping: etale abelian image, etale ordinary derived Hom image, and pro-etale ordinary derived Hom image. Source: Stacks 03PL/0A45. This keeps the repeated ordinary-class type transports out of the long uniqueness predicate. `divisorEtaleHom` is simply `Ext.hom` into the existing etale supported model and belongs to the separate etale-Hom node. No mathematical operation has changed.

`def-pur-framed-etale-hom` separately owns the canonical `Ext.hom` wrapper into the existing supported Hom model. Its source is the ordinary derived category/Ext API; it has no theorem or chosen localization. All fifteen delivered modules compiled through the prescribed scompile wrapper with no errors or unexpected warnings in the final compile11 run.

Dry-run repair: citations with multiple node ids in one bracket were rewritten as individual bracketed ids, and the generic helpers now bind their universes in an explicit `universe u v w` command so the declaration scanner records the same names Lean elaborates. The item still differs from the base only in `lean` and the allowed additions to `stmt_deps`.



`def-pur-ordinary-hom-site-comparison` owns the existing
WeilConjectures.PurityFiniteSetting.functorialCupOrdinaryCompare in
Sheaf.Paper.SupportedCupFunctoriality. Its statement spells out exact inverse image,
the inverse degree-zero constant comparison, and the target shift/twist comparison.
Source: Stacks 099W/09B1. def-pur-supported-hom-site-comparison owns only its supported
analogue, so a second node is needed for this existing ordinary map.

`def-pur-supported-hom-pair` owns the existing AlgebraicGeometry.SupportHomPair,
sections/group/complex/cycleClass/derivedHom/cocycleMorphism/Identification and the
etale/proEtaleSupportHomPair presentations in Sheaf.Paper.SupportedHomPullback.
Source: Milne section 9, Theorem 9.4 and its Ext proof, pp. 66–67, Example 9.5.
def-pur-supported-hom-cocycle-data owns the generic normalization used internally;
it does not own this pair's site data, support-group abbreviation or Identification
interface. The new record reuses them without a module or theorem assertion.

For both nodes the repair ran msearch LeanSearch (supported cohomology/derived Hom
normalized at one: eight generic hits), LeanFinder (ordinary etale/pro-etale exact
comparison: eight unrelated etale-algebra hits) and Mathlib grep
SupportHomPair|proEtaleSupportHomPair|functorialCupOrdinaryCompare (zero hits).
Project/DAG rg found the actual declarations but only theorem-node ownership.
blueprint_refs.py search returned zero 'supported Hom' and fourteen 'site comparison'
matches, none owning these interfaces. The raw search results are in each new node.

## Returned-delivery repair

The immutable returned head f8b5f55a63a7 was reported mathematically faithful. The saved
packet first passed deliver2.py --no-push at c8b48849fa7 against the current live base;
its independent-return H2 citation defect nevertheless remained in the saved JSON.
This repair changes DAG ownership/citations and this report. All fifteen Lean files,
all signatures and the item's original statement and proof remain unchanged.

The six affected definition nodes are def-pur-framed-etale-hom,
def-pur-framed-forget-support, def-pur-framed-pro-predicate,
def-pur-framed-realization-pullback, def-pur-framed-realization-enlarge and
 def-pur-framed-realization-property. Their references to plain supported groups,
forgetting support, pullback and change of support now cite
 def-pur-supported-class-operations. The pro-predicate cites
 def-pur-supported-hom-site-comparison for functorialCupCompare and
 def-pur-supported-hom-pair for the normalized Identification and actual support group.
The realization-property cites def-pur-ordinary-hom-site-comparison for the ordinary
comparison. The item cites these owners too. No theorem is used as the definition
owner for these interfaces.

The theorem nodes and their proof dependencies are retained in the library. In
particular supportedHom_pullback remains the existence/naturality theorem rather
than a definition of Identification; supportedCupFunctoriality remains the theorem
of compatibility laws rather than the definition of its maps. Their mathematical
uses remain proof ingredients, described in divisorRealization_pullback and the
main theorem's proof plans. Definition-node proof/proof_deps remain [] as explicitly
required by brief-stage2 section 5. The item's accepted proof/proof_deps are unchanged;
no source-statement correction is needed to fix ownership.

The returned advisory about empty proof_deps on new definition nodes is constrained
by that same field rule. The existsUnique helper theorems remain named, sorry-only,
with their complete proof plans in the owning node's module; the corresponding node
statement explicitly includes their unique characterization. kummerδ₁ and
etaleIsoTorsor remain provided by lem-amb-kummer-any-base and
lem-sc-line-bundle-torsor, already cited by the scalar-maps/integral-extension/transport
nodes. No new private copy of these maps or of classH1 was introduced. The hW binders
are unchanged: they identify the complements needed to type the already checked
frame maps, and add no geometric restriction.

## Second reading by Q106

This is the repairing worker's explicit self-check, not an independent reading by
another agent; the dispatcher forbids starting agents. The independent maintainer
reading is the returned entry quoted in the assignment. I compared the saved node
statements, their signatures and the actual definitions in SupportedCupFunctoriality
and SupportedHomPullback. The mismatch found was exactly H2: theorem ownership of
plain data. The changes above repair that mismatch without changing Lean.

The finite datum still binds positive n and the same coefficient ring and root
presentation. The scheme hypothesis still means separated finite type over k;
the support remains any closed immersion. The frame still belongs to the actual
Isom torsor on the complement, and the relative extension still uses supported
integer one and its specified zero frame. The scalar equation is still the positive
Yoneda splice followed by the identical root tensor map. DivisorProGroup is still
the actual supported right-derived group, and DivisorProRealizes still quantifies
over every cocycle-normalized Identification with functorialCupCompare as its
right-hand side. The companion statements still assert framed-isomorphism
invariance, arbitrary etale pullback, support enlargement and zero/addition
preservation. Both ordinary forget-support equations still use the positive
Kummer image and identical ordinary comparison. Empty scheme/support/complement,
identity pullback, equal supports, non-Cartier support and nonextendible frames
remain allowed. The new existing:true records assert no existence, bijectivity
or compatibility theorem and change no definition or universe.

