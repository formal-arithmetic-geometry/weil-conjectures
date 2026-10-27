## Worker report

The module `Sheaf.AlgebraicGeometry.GroupoidStrictLocalReducedOrbit` states
`AlgebraicGeometry.groupoid_strictLocal_reducedOrbit`, with its sole proof `sorry`.
There are no new definitions, dependency repairs, or statement corrections. The node's
natural-language statement and every non-Lean field are unchanged.

I read Stacks `groupoids.tex`, Tag 0DT9 (`lemma-etale`), the lemma's hypotheses and the
first part of its strictly henselian claim through the definition of J'. The reduced
ring identification is the finite Chinese remainder consequence described in the node.
The current blueprint unit's six-functor statement is not changed. The example
CompactObject module is now withdrawn; the delivered file follows the current module
header convention and the extant SchemeGroupoidLaws example instead.

The following matches each hypothesis and clause to its Lean expression.

| Node | Lean |
| --- | --- |
| Base scheme S | `S : Scheme.{u}` |
| U = Spec A, R = Spec B, U' = Spec A', R' = Spec B' | Four `CommRingCat.{u}` parameters and their actual `Spec` objects everywhere; no unspecified affine presentations |
| The eight structure maps for each groupoid | `s,t,e,i,c` and their primed versions, with `c : pullback s t ⟶ Spec B` and the analogous primed composition |
| The groupoid laws | `_hG : Scheme.IsGroupoid s t e i c` and `_hG'` using the recorded dependency |
| Groupoids over S | `π,π'` and `_hS,_hS'` say source and target have the same composite to S; the arrow structure map is `s ≫ π`, respectively `s' ≫ π'` |
| F has object and arrow maps a,b and is over S | `a,b,_ha`; source and target compatibility is included in the commutativity fields of `_hs,_ht` |
| F respects identities, inverses and composition | `_he,_hi,_hc`; the last quantifies over every test scheme and pairs of pullback-valued points with corresponding projections |
| All four source/target maps finite locally free | `[s.IsFiniteLocallyFree]`, `[t.IsFiniteLocallyFree]`, `[s'.IsFiniteLocallyFree]`, `[t'.IsFiniteLocallyFree]` |
| a etale | `[Etale a]`, using the recorded Mathlib spelling |
| Source and target squares cartesian | `_hs : IsPullback b s' s a` and `_ht : IsPullback b t' t a` |
| G and G' are the diagonal stabilizers, and their square is cartesian | `_hstab`: for every scheme H, a point x of U', and an arrow r of R whose source and target are both `x ≫ a`, there is exactly one arrow r' with image r and both endpoints x. By the two defining fibre-product universal properties and Yoneda, this is precisely `G' ≅ G ×_U U'` over both factors. This retains scheme-theoretic loops, not just ordinary/geometric point stabilizers. |
| C and C' are the invariant subrings | `C,C' : Subring ...` with `_hC,_hC'` equating them to `RingHom.eqLocus` of the recorded affine ring maps `Spec.preimage` |
| Canonical homomorphism C → C' | `φ` with `_hφ : C'.subtype.comp φ = (Spec.preimage a).hom.comp C.subtype`; the inclusion determines it uniquely. Source/target compatibility ensures existence: restrict `a*` to the equalizer. This is a presentation of the canonical map, not an arbitrary comparison assumption. |
| C strictly henselian local, m its maximal ideal | `[IsStrictlyHenselianLocalRing C]`; m is always the actual `IsLocalRing.maximalIdeal C` |
| p' is a prime of C' over m | `p' : PrimeSpectrum C'`, `_hp' : PrimeSpectrum.comap φ p' = IsLocalRing.closedPoint C` |
| Z and Z' are the sets over m and p' | `_hZ,_hZ'` equate the named sets with the corresponding fibres of `PrimeSpectrum.comap` of the subring inclusions |
| Z and Z' nonempty | `Z.Nonempty` and `Z'.Nonempty` |
| Both sets finite | `Z.Finite` and `Z'.Finite` |
| Every point of both sets closed in its ambient spectrum | The two clauses `∀ x ∈ Z, IsClosed ({x} : Set (PrimeSpectrum A))` and its primed counterpart |
| a : Z' → Z is a bijection | `Set.BijOn a Z' Z`, including that a maps the selected primed fibre into the unprimed fibre |
| The original residue field map is an isomorphism at every selected point | `∀ x ∈ Z', IsIso (a.residueFieldMap x)`; these are exactly the recorded scheme residue fields and induced maps |
| J = radical(m A) | `(Ideal.map C.subtype (IsLocalRing.maximalIdeal C)).radical` |
| J' is the intersection of the primes in Z' | `⨅ x : Z', x.val.asIdeal` |
| The induced A/J → A'/J' is an isomorphism | `∃ ψ : (A ⧸ J) ≃+* (A' ⧸ J'), ψ.toRingHom.comp (Ideal.Quotient.mk J) = (Ideal.Quotient.mk J').comp (Spec.preimage a).hom`, with J and J' expanded. The equation determines the map uniquely on the surjective quotient projection and includes its well-definedness. |

The equality parameters C,C',Z,Z' simply name fully specified constructions, with no
`let` or hidden `show` binder in the statement. Given the node's data, choose precisely
those equalizers and fibres, and the canonical invariant map; every binder is then
available. Conversely, the displayed equalities force those objects and maps to be
the ones in the node. No arbitrary object, extra mathematical assumption, rank bound,
Noetherianity, or finite-dimensional residue extension has been substituted.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`,
  `Spec.map`; `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage`.
- `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`: `AlgebraicGeometry.Scheme.IsGroupoid`
  (the full signature, docstring and eleven laws were read).
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`, extending finite, flat, lfp.
- `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`: `pullback`, its projections,
  and universal property, imported through SchemeGroupoidLaws.
- `WeilConjectures.Mathlib.RingTheory.Henselian`: `IsStrictlyHenselianLocalRing`, with
  henselian-local parent and separably closed residue field.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField` and
  `Scheme.Hom.residueFieldMap`.

The stated proof dependencies are imported privately, including both affine groupoid
integrality and orbit-fibre modules, finite-fibre geometry, algebraic residue extensions,
pure inseparability, GeometricLifts, radical/intersection identities, and Chinese remainder.
The orbit-fibre module currently uses the equivalent recorded `IsGroupoidScheme` interface;
its laws were read, and translating the supplied `Scheme.IsGroupoid` equations to those
laws in a future proof is elementary. No dependency record is changed or duplicated.
The theorem docstring carries all six proof steps with the dependency node IDs.

Edge cases checked before writing:

- Empty U or R / zero coordinate rings: a strictly henselian local invariant ring is
  nontrivial, so an empty unprimed object scheme is incompatible with the hypotheses;
  existence of p' over the maximal ideal and integrality ensure the primed fibre is
  nonempty. No nonemptiness hypothesis was added.
- With A = k separably closed and A' a nonempty finite product of copies of k, use
  identity groupoids on both sides. A selected component of the primed invariant spectrum
  has the expected closed point; J' intersects the selected fibre, not all points of U'.
- Multiple orbit points (for example a transitive finite discrete group action), and
  varying or zero local ranks on components: no singleton, positive-rank or constant-rank
  assumption occurs; `Set.BijOn` retains the whole orbit.
- Infinite algebraic purely inseparable residue extensions are allowed. No finite module
  or perfectness hypothesis appears. Characteristic zero and positive characteristic
  are both included.
- Nonreduced arrow schemes and nonreduced test schemes: `_hstab` quantifies over all H
  and equalities of morphisms, not just geometric point stabilizers.
- All rings and schemes use the same ambient universe u, as the source category of
  schemes does; no independently smaller test universe is imposed. Quotients, subrings,
  primes and residue fields have their canonical universes. `autoImplicit` is false.

Searches made (all on 2026-10-24):

- `msearch.py ... leanfinder`: "An etale cartesian stabilizer preserving morphism of
  affine groupoids induces isomorphic reduced closed orbit fibres over a strictly
  henselian invariant ring". Eight hits: profinite invariant stabilizers, pre-Galois
  categories, etale algebras, and scheme fibres; none states this groupoid theorem.
- `msearch.py ... loogle`: `"Groupoid", "Etale"`. Zero hits.
- `msearch.py ... grep`: `groupoid.*(stabili|orbit)|stabili.*groupoid`. Two unrelated
  Mathlib subgroupoid docstring hits; no match.
- `msearch.py ... leansearch`: "Reduced closed orbit fibres of a stabilizer preserving
  etale map of finite locally free affine groupoids over strictly henselian invariants".
  Eight hits concern actions, etale base change, finite fibres and reduced schemes;
  none is this statement.
- `rg` of the same groupoid/stabilizer/orbit patterns in `lean/WeilConjectures` and
  `lean/Sheaf`, and `grep -rn` of this item's ID in `lean/WeilConjectures`. No upstream
  statement. The project has AffineGroupoidEtaleInvariantComparison, which proves the
  full Tag 0DT9 comparison and cites this item as a proof prerequisite. It does not
  already state the selected reduced-orbit assertion. Its full signature/docstring
  were read; the explicit morphism and stabilizer hypotheses here follow that interface.
- `rg` of `strictLocal_reducedOrbit|groupoid_strictLocal|reducedOrbit` in
  `dag/lean_names_upstream.json` and both source trees: no existing declaration name.
  Searches of the DAG and project for invariant and groupoid morphism interfaces found
  the recorded equalizers and the comparison theorem above. Mathlib's `RingHom.eqLocus`
  already supplies the invariant subring; no new notion/node is necessary.

Validation: `scompile.py Q11 lem-sfb-groupoid-strict-local-reduced-orbit` compiled the
file both in sandbox mode and as its library module, cleanly (10.2 s / 8.4 s). The only
postponed proof is the named theorem. The prescribed `deliver2.py --no-push` dry run
passed preflight and compilation, printing OK (commit d6492d36dc1).

## Second reading by Q11

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
