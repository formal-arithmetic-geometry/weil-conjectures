## Worker report

Stage 2, Q18: the item is stated by
`AlgebraicGeometry.curve_trace_cup_naturality` in
`Sheaf.AlgebraicGeometry.Curve.TraceCupNaturality`. Its only theorem proof is `sorry`.
The original mathematical statement, proof and proof dependencies are unchanged.
One definition node is added to `stmt_deps` for the finite coefficient action cup.
All definitions have real data. No arbitrary cohomology maps or arbitrary coefficient
isomorphisms stand in for the specified maps.

Hypothesis and clause correspondence, read with the module open:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The curves and their structure maps are `C D`, `fC fD`, each with
  `[IsConnectedCurve] [Smooth] [IsProper]`. `IsConnectedCurve` includes finite type,
  separatedness, connectedness, nonemptiness and dimension one. The named maps are
  needed for the semilinear square and the recorded curve definition.
- The prime and characteristic condition are `ell c`, `[Fact ell.Prime]`,
  `[CharP k c]`, and `hell : ell ≠ c`, including characteristic zero.
- The level-n constant sheaf is `C.constantZMod (ell ^ n)` (and similarly D),
  the existing constant sheaf of `ULift (ZMod (ell ^ n))`. The twisted sheaf is the
  existing `rootsOfUnitySheaf`, the kernel of the power map on `gmSheaf`.
- All groups are the recorded ordinary small-etale `Sheaf.H` convention; no compact
  supports, pro-etale cohomology, finite-field datum, Frobenius or selected generator
  of roots of unity is introduced.
- `trC trD` are additive maps specified by their defining normalization `htrC htrD`.
  For every positive n and closed point P the value on `curvePointKummerClass` is 1.
  That helper applies the actual Kummer boundary to the actual Picard class
  `Pic.ofClosedPoint k P = [I_P^dual] = [O(P)]`. This is the point divisor line bundle,
  not an arbitrary invertible module. `DivisorClassCurve` identifies the existing
  point-divisor Picard construction with the associated divisor modules recorded by
  `def-sc-divisor`; both modules are imported. Normalization determines trace, since
  the Kummer point classes generate H² (the item's Steps 1 and 4).
- The normalization quantifies `hn : IsUnit ((ell ^ n : Nat) : Γ(C,top))` rather than
  assuming a separate invertibility hypothesis. Such witnesses exist from `hell`:
  ell is nonzero in k, and its powers map to units under the structure morphism on
  global sections. Proof irrelevance makes this independent of the witness.
- `cupC cupD`, with `hcupC hcupD`, specify the canonical coefficient-action cup,
  through `IsFiniteEtaleCup`. Its equation uses *all* module-extension representatives
  under the canonical comparison to ordinary abelian-sheaf cohomology. The comparisons
  are constructed by exact forgetting and precomposition with the constant integer
  unit, not supplied as arbitrary equivalences. The Z/N action on an N-torsion
  abelian sheaf is unique. In the module category the first coefficient is the
  tensor unit; tensor of the two derived classes followed by evaluation equals
  their Yoneda composite in the displayed order. Thus this is a concrete
  characterization of the requested product, not a naturality hypothesis.
- `curveTraceCup` is precisely trace of cup. Binding natural i,j with `hij : i+j=2`
  gives exactly (0,2), (1,1), (2,0), equivalently the node's i=0,1,2 with j=2-i.
  The equality merely reindexes the output group before applying trace.
- The first conjunct binds `1 ≤ m` and `hmn : m ≤ n`, hence n≥m≥1. Its untwisted
  map is `Sheaf.H.map (curveConstantReduction ...)`; the definition is exactly the
  constant-sheaf image of `ZMod.castHom (pow_dvd_pow ell hmn)`.
- Its twisted map is `Sheaf.H.map (curveRootsReduction ...)`. The kernel lift
  restricts `ell^(n-m)` times the identity on the additively written unit sheaf,
  so it is exactly z↦z^(ell^(n-m)). The defining kernel relation follows from
  ell^m * ell^(n-m)=ell^n. The RHS reduces the original pairing value with the same
  `ZMod.castHom`. This is the first displayed equation of the node.
- The second conjunct binds all positive n and the same three degree pairs.
  `σ : k ≃+* k`, `f : D ⟶ C`, `[IsIso f]`, and
  `hσ : f ≫ fC = fD ≫ Spec.map (CommRingCat.ofHom σ)` give any semilinear scheme
  isomorphism, with no requirement that σ be trivial or come from a finite field.
- Both pullback maps start with the recorded `Etale.cohomologyMap` for the actual f.
  Constant coefficients use the actual `Scheme.upperStarConstantSheafIso`.
  Twisted coefficients use `curveRootsPullback`, the kernel restriction of the
  actual `upperStarGmSheafToGmSheaf f`. Thus its identification is the canonical
  roots-of-unity pullback, not a parameter which could be multiplied by a unit.
  The equality is exactly the second displayed equation of the node.

Dependency declarations used:

- `Sheaf.AlgebraicGeometry.SmoothConnectedCurveLocalRings`: the existing
  `Scheme.smooth_connected_curve_local_rings`, deriving integrality for the point
  class construction; no additional integral/irreducible hypothesis is assumed.
- `WeilConjectures.AlgebraicGeometry.Curve`: `IsCurve`, `IsConnectedCurve`,
  `IsConnectedCurve.krullDim_eq_one`; the original curve API is retained.
- `WeilConjectures.AlgebraicGeometry.Sites.Kummer`: `rootsOfUnitySheaf`,
  `kummerSequence`, `kummerSequence_shortExact`, `constantZMod`, `kummerδ₁`.
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`: the recorded
  `Etale.cohomology`/`rightDerivedGlobalSections` framework; `Sheaf.H` is its
  accepted source convention, with the already recorded stage-3 comparison.
- `Sheaf.AlgebraicGeometry.DivisorModule`: `Divisor.moduleOfSmoothConnectedCurve`;
  `Sheaf.AlgebraicGeometry.DivisorClassCurve`:
  `Scheme.exists_divisorClassGroup_addEquiv_pic_associatedModule`.
- `WeilConjectures.AlgebraicGeometry.Curve.Picard`: `Pic.ofClosedPoint`;
  `WeilConjectures.AlgebraicGeometry.Sites.GmPicard`:
  `Pic.toCohomologicalPicardGroup`; `Sites.Gm`: `upperStarGmSheafToGmSheaf`.
- `SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`:
  `Etale.cohomologyMap`, `Scheme.upperStarConstantSheafIso`.
- Mathlib: `CategoryTheory.Abelian.Ext.comp`, `Ext.mk₀`, `Ext.mapExactFunctor`,
  `constantSheaf`, `sheafCompose`, `sheafifyLift`, `kernel.lift`,
  `kernel.condition`, `ZMod.castHom` and `pow_dvd_pow`.
- Proof-plan imports also include the recorded `SecondKummerDivisors`,
  `GmPicardPullback`, `RightDerivedTriangleConnecting`,
  `RightDerivedUniversalDeltaFunctor` and `PullbackCohomologyLongExactLadder`.
  The general cup-functoriality node has no recorded Lean module to import.

Edge cases checked: n=m gives the identity coefficient and power maps, m=1 is
included, and the three degree pairs are exact with no negative-degree truncation.
Characteristic zero and ell=2 are allowed. Identity f and σ are included, as are
nontrivial ground-field automorphisms. Genus zero and zero cohomology classes do not
require extra hypotheses. Empty and disconnected schemes are excluded precisely
by the stated connected-curve assumption, not by extra conditions. The helper
predicate also makes sense for N=0 or 1; the main theorem uses only positive powers
of a prime at positive levels.

Searches: `msearch.py` LeanFinder query “Naturality of trace cup product pairings on
etale cohomology of proper curves under maps of finite coefficients and automorphisms
of the ground field” returned cotangent, field trace and Galois-cohomology results,
not this statement. Loogle “Etale.cupProduct, Sheaf.H.map, traceMap” returned no match;
Mathlib grep “trace.*cup|cup.*trace|curve_trace_cup” in AlgebraicGeometry returned no
match. Direct searches of Mathlib, WeilConjectures and lean/Sheaf found no exact
statement and no existing declarations with the new names; `dag/lean_names_upstream.json`
was also checked. The existing upstream `Etale.cupProduct` is for two untwisted unit
coefficients in its derived category, and does not directly supply this twisted
ordinary-cohomology interface. It was read, including its equality to the Yoneda
unit product. The further searches for the new helper are recorded below and in
its node. Read the local Milne PDF §14 and §22 and the local Stacks cup section.

No statement dispute or correction. Every universe is explicit and autoImplicit is
false. The complete nine-step proof from the DAG is in the theorem docstring.

## New nodes

`def-wf-finite-etale-cup` defines the representative characterization of the finite
constant coefficient action cup. Its helpers construct the constant rank-one module,
the exact forgetful functor, the canonical sheafified constant-section map and the
comparison of module extensions with ordinary cohomology. Structural exactness
instances are built using existing local-surjectivity and exact-functor API; no
postponed data or helper theorem is introduced. Source: Milne §22 p.135 and Stacks
0FPJ, specialized to constant Z/N and its tensor unit. A new definition is needed
because the existing field-linear O_X-module cup, finite-field Poincare trace cup,
and general bilinear cup-naturality theorem are different interfaces.

LeanSearch query “Cup product on sheaf cohomology with constant finite ring
coefficients equals Yoneda composition of extensions of the constant rank one module”
returned `Sheaf.H`, cohomology presheaves, free Yoneda and module generators, with no
cup construction. Loogle “CategoryTheory.Abelian.Ext.comp,
CategoryTheory.Abelian.Ext.mapExactFunctor” returned generic Ext comparison and
adjunction lemmas, which are reused. Mathlib grep “Yoneda.*cup|cup.*Yoneda|IsFiniteEtaleCup”
in CategoryTheory returned zero. Direct searches in all three source trees for
`IsFiniteEtaleCup|finiteEtaleClass|finiteEtaleModuleUnit` returned zero. DAG and
blueprint searches found only the distinct interfaces described above. Search output
counts and declaration names are retained in the new node's mathlib_searches.

## Second reading by Q18

Performed a separate pass with both JSON statements, both Lean modules, the source
cup formula and dependency declarations open. This is a self-review; the dispatcher
explicitly forbids starting another agent, and the maintainer performs the independent
review. Found and repaired the initial draft's missing trace normalization,
unconstrained cup and reduction maps, arbitrary roots-of-unity isomorphism, missing
`IsIso f`, and absent positive-level restriction in the semilinear clause. Replaced
these with the normalization, concrete representative cup characterization, actual
kernel maps and explicit isomorphism/level conditions described above. Checked each
binder and both equations against the correspondence list. The auxiliary node's
representative condition is stated verbatim by its predicate; its construction uses
existing Mathlib Ext and sheafification, and its common lifted coefficient universe
adds no equality between independently quantified universes.

Validation: all delivered files are checked with scompile.py; the required deliver2.py
dry run and delivery follow after the final clean compilation.


## Maintainer independent reading, 2026-10-18

The immutable delivery was independently read against its five statement dependencies,
Milne §§14 and 22, Stacks 0FPJ/0H9A, and the exact Lean declarations. The mathematical
target statement and its Lean signature are retained verbatim. The original report's
assertion that no helper constructions existed is superseded by this finding and fix.

H4: the constant rank-one module, scalar-forgetting functor and ordinary class comparison
already exist as `Etale.ordinaryFiniteConstant`, `Etale.RawModuleScalarComparison.forget`
and `Etale.ordinaryFiniteClass`. The latter comparison uses the canonical integral
generator `Etale.ordinaryFiniteIntegralGenerator`, sending one to one. The replacement
FiniteEtaleCup module reuses these declarations (at `ULift (ZMod N)`) and removes the
duplicate definitions and locally proved exactness instances. Only the sheafified
constant-section comparison `finiteEtaleUnitMap` and `IsFiniteEtaleCup` remain new.
The helper node now cites both owning nodes and records this search. This is an API
reuse repair; no source-based mathematical statement correction is needed.

All the hypothesis/clause correspondences in the original report were independently
checked: algebraically closed field; smooth proper connected dimension-one curves;
prime unequal to characteristic (including zero); positive levels; degree-two trace
normalization via the actual Kummer/Picard point class; the derived action cup in the
Yoneda order x then y; actual coefficient and roots-power reduction; all three degree
pairs; actual canonical pullback along the semilinear scheme isomorphism; both equations.
The comparison from module extensions is an isomorphism onto ordinary cohomology for
the constant free rank-one source (Milne p.102). Thus the representative predicate
determines cup on every input for the roots sheaf, rather than assuming naturality or
leaving an arbitrary map. The integral generator in the reused interface is the same
canonical map as reduction followed by the constant-section comparison.

Checked n=m, m=1, characteristic zero, ell=2, identity and nontrivial semilinear
isomorphisms, genus zero, zero classes, and the three degree pairs. Empty, disconnected
and dimension-zero schemes are excluded by the node's own connected-curve convention.
The common coefficient lift u+1 matches the small-etale site and recorded pullback API;
no extra universe equality is imposed. Auto-implicit is disabled and all binders bound.
Both required original report headings are retained. Module and declaration docstrings
identify sources and blueprint nodes; the target docstring gives all nine proof steps.
All definitions have real data; the sole new theorem has exactly the proof `sorry`.
After this repair the new helper module contains no local proofs. There is no pro-etale
substitution or dropped route-pivot machinery, and the cited IDs avoid the dropped list.

Compilation: the original two siblings passed a completed scompile.py overlay/server
confirmation run, exit 0, with no diagnostics (FiniteEtaleCup 28.9s library,
TraceCupNaturality 24.7s library). The replacement helper and unchanged target are
checked together through the same wrapper; the completed result is recorded in review.md.
No global build, direct SSH, repository edit, branch mutation, claim or delivery was run.

Final replacement compilation completed with exit 0 and no diagnostics: helper
private overlay 56.5s, preliminary 45.6s, sandbox 28.5s, library confirmation
24.3s; unchanged target sandbox 19.7s, library confirmation 17.1s. All were
within the 60-second limit. The final helper has only the two new definitions
and its `lean.statement` remains verbatim. Complete fixes use the module path,
whole new-node JSON, and whole report formats accepted by merge_delivery.py.
