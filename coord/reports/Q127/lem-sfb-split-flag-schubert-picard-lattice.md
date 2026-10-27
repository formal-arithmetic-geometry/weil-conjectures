## Worker report

The module `Sheaf.AlgebraicGeometry.SplitFlagSchubertPicardLattice` states
`AlgebraicGeometry.SplitFlagSchubert.split_flag_schubert_picard_lattice`, with its
only theorem proof `sorry`. The two real auxiliary definitions are `divisorClass`
and `BoundaryBasis`; neither chooses data from an existence theorem. No node statement,
statement dependencies, or proof dependencies were changed. No new DAG nodes or dependency
repairs are needed.

Source read: Brion, *On Linearization of Line Bundles*, Lemma 2.3, printed p.118,
https://www.ms.u-tokyo.ac.jp/journal/pdf/jms220104.pdf, especially the paragraph after
sequence (2): the flag Picard group and characteristic map are described by the root datum,
which is unchanged by field extension. The six-step DAG proof supplies the explicit
Schubert-boundary construction, including its Milne Lemma 18.21 reference. The named
literature PDFs are absent in this read clone, so Brion was read directly from its recorded URL.

Hypotheses, individually:

- `F : Type u`, `[Field F]`: arbitrary field, with no characteristic, perfection, or
  algebraic-closedness restriction.
- `H T B : Grp (Over (Spec (.of F)))`: the three group schemes, with genuine group laws.
- `hH : ReductiveTorusCentralizer.IsReductive H`: smooth affine finite type,
  geometric connectedness, and absence of a nontrivial smooth connected normal unipotent
  subgroup over the algebraic closure. The dependency expands these conditions explicitly.
- `iT` and `hT : ReductiveTorusCentralizer.IsMaximalTorus iT`: the closed maximal torus
  inclusion, with its maximality quantified over torus subgroup factorizations.
- `hsplit`: an integer rank `r : ℕ` and a group-scheme isomorphism from `T` to the
  recorded `MultiplicativeType.splitTorus F r`, including rank zero.
- `iB`, `hB`: closed subgroup, smoothness, connectedness, the recorded finite-series
  `SolvableGroupStructure.IsSolvable B`, and maximality among such subgroup inclusions.
  A factorization `f : B ⟶ C` over the two inclusions must be an isomorphism. This is
  exactly maximality, since both subgroup embeddings are monomorphisms. The existing
  `IsBorelGroupScheme` was read but requires `[IsAlgClosed F]`; using it here would exclude
  fields in the statement. The condition is expanded in this theorem, without defining
  a competing Borel predicate or changing that older definition node.
- `hBsplit : IsSplitSolvable B`: the existing smooth connected split-series predicate,
  with the actual represented fppf quotients `G_a` or `G_m` at each step.
- `jT`, `hjT`: `T ⊆ B`, with `jT ≫ iB = iT` fixing the chosen embeddings.
- `Q`, `q`, `hqflat`, `hqsurj`, `hqlfp`, `hqtorsor`: a presentation of the represented
  fppf coset sheaf. A flat surjective locally finitely presented map is an fppf cover;
  its kernel pair is precisely `(h,b) ↦ (h,hb)`. Thus its sheaf quotient is the
  sheafification of `H(A)/B(A)`. Conversely the canonical quotient by a smooth
  finite-type Borel has these properties. No normality of B is imposed, and Q is
  not given a group structure. This is the standard torsor presentation of the
  object introduced by “let Q = H/B,” rather than an extra restriction on H or B.

Conclusions, individually:

- Existential `d s : ℕ` allows both to be zero.
- `j` has domain the recorded `AffineSpace (ULift (Fin d)) (Spec F)` with its
  canonical map to `Spec F`. Its being a morphism in `Over` makes the cell defined over F.
- `BoundaryBasis` starts with `IsOpenImmersion j.left ∧ DenseRange j.left`.
- `D : Fin s → Q.left.IdealSheafData` specifies actual quasi-coherent ideals;
  `hD` states that each is an effective Cartier ideal in the recorded sense.
  The closed subscheme is `(D i).subschemeι`, so no arbitrary support structure is used.
- `GeometricallyIntegral ((D i).subschemeι ≫ Q.hom)` says that each divisor remains
  nonempty, reduced and irreducible after every field extension.
- Injectivity of `i ↦ (D i).support` gives distinct supports.
- The `∀ Z` equivalence in `BoundaryBasis` identifies exactly the codimension-one
  irreducible components of the complement. Components are `irreducibleComponents`
  of the complement subtype, their images in Q are `Subtype.val '' C`, and codimension
  one is `ringKrullDim` of the local ring at a generic point being 1. Components of a
  closed subset of a scheme have generic points; this universal condition is consequently
  not vacuous. It is the same local-ring form used by the recorded affine-boundary lemma.
- `divisorClass I hI` is `Scheme.Pic.ofIsInvertible I.toModulesᵛ`, using the recorded
  proof `hI.isInvertible_dual_toModules`. Thus it is exactly `[O_Q(D)] = [I_D^∨]`.
- The equivalence `Multiplicative (Fin s → ℤ) ≃* Q.left.Pic`, together with its value
  on EVERY exponent tuple, gives exactly the tensor-power map from Z^s. `Pic` uses
  multiplicative notation: multiplication is tensor, inverse is dual, and integer
  exponentiation is the required positive or negative tensor power. The product is
  finite and includes the empty product.
- `IsIso iT → d = 0 ∧ s = 0 ∧ Nonempty (Q ≅ Over.mk (𝟙 (Spec F)))` gives the stated
  H = T case intrinsically, including H = 1. This is the identity-base object in `Over`.
- The final `∀ (L : Type u) [Field L] [Algebra F L]` quantifies over every extension
  in the same universe as the schemes. The universe `u` is arbitrary and cumulative;
  no finite generation or algebraicity is imposed on L. In particular L = F is allowed.
- The cell is the actual image of `j` under `Over.pullback (Spec.map (algebraMap F L))`.
  Its domain is the scalar extension of affine d-space, canonically affine d-space
  over L by the affine-space base-change universal property.
- `hDL` concerns exactly `(D i).comap p_Q`, the actual closed-subscheme base change,
  not divisors selected afresh. `BoundaryBasis` applied to these data repeats all
  immersion, density, geometric-integrality, distinctness, component, and basis clauses.
- The last equality uses `Scheme.Pic.mapHom p_Q` and equates the original dual-ideal
  class with the dual-ideal class for that exact comap ideal. This is the stated
  pullback compatibility, with the same finite index set and basis. The extended
  quotient is the pullback scheme; fppf torsors and their right-B kernel pairs
  base change, giving its canonical identification with H_L/B_L.

Dependency declarations read and reused:

- Mathlib `Field` (Algebra.Field.Defs), `Algebra` (Algebra.Algebra.Defs), and
  `CategoryTheory.GrpObj`/`Grp` (CategoryTheory.Monoidal.Grp).
- `Smooth` (AlgebraicGeometry.Morphisms.Smooth), `ConnectedSpace`
  (Topology.Connected.Basic), `LocallyOfFiniteType` and `QuasiCompact`
  (AlgebraicGeometry.Morphisms.FiniteType / QuasiCompact). They occur inside the
  recorded group predicates, rather than being restated as extra hypotheses.
- `ReductiveTorusCentralizer.IsReductive` / `IsMaximalTorus`
  (Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology).
- `MultiplicativeType.baseChange` / `splitTorus` / `IsTorus`
  (Sheaf.AlgebraicGeometry.ToriMultiplicativeType).
- `SolvableGroupStructure.IsAlgebraic`, `IsUnipotent`, `IsSolvable`, and
  `IsFppfQuotient` (Sheaf.AlgebraicGeometry.SolvableGroupStructure).
- `IsSubgroupScheme`, `IsNormalSubgroupScheme`, `IsClosedSubgroupScheme`
  (WeilConjectures.AlgebraicGeometry.GroupScheme.Defs).
- `IsSplitSolvable`, `SplitSolvableLength`, and `RepresentedRightTorsor`
  (Sheaf.AlgebraicGeometry.SplitSolvableTorsorDefinitions), using the existing
  `StandardGroupSchemes.additive`, `multiplicative`, and their group laws
  (Sheaf.AlgebraicGeometry.StandardGroupSchemes).
- `pullback`, `pullback.fst`, `pullback.snd` (Mathlib.CategoryTheory.Limits.Shapes.
  Pullback.HasPullback), and `Over.pullback`.
- `Scheme.Modules.IsInvertible` (WeilConjectures.AlgebraicGeometry.Modules.Invertible),
  and the recorded tensor inverse image in
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction (which publicly imports
  WeilConjectures.AlgebraicGeometry.TensorPullback). Picard pullback uses the existing
  Scheme.Pic.mapHom, rather than constructing a new class map.
- `IsOpenImmersion` (Mathlib.AlgebraicGeometry.OpenImmersion), `AffineSpace` and its
  canonical `over` instance (Mathlib.AlgebraicGeometry.AffineSpace).
- `Scheme.IdealSheafData.IsInvertible`
  (WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible),
  `.toModules` (WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module),
  `Scheme.Modules.dual` (WeilConjectures.AlgebraicGeometry.Modules.Dual), and
  `IsInvertible.isInvertible_dual_toModules`
  (WeilConjectures.AlgebraicGeometry.EffectiveCartier).
- `Scheme.Pic.ofIsInvertible`, the Picard commutative group and `.mapHom`
  (WeilConjectures.AlgebraicGeometry.Picard.Group).

All already stated proof dependency modules are imported privately, except where their
notions are also public statement data. Mathlib leaves for UFD height-one primes, affine
opens/stalk localization, tilde localization, properness and Krull dimension are imported
through their owning modules. At the time of writing, the three proof nodes
`lem-sfb-split-bruhat-affine-stratification`,
`lem-sfb-scheme-image-flat-base-change`, and
`lem-sfb-stalk-nonzerodivisor-cartier-spreading` have no recorded Lean declarations;
they are mentioned by exact node id in the proof docstring and not imported under
invented names. They are proof prerequisites only and are not needed to type the statement.

Edge cases checked before writing: torus rank zero; H = T; H = 1; d = s = 0;
empty divisor index set; negative exponents; the identity field extension; transcendental
and inseparable extensions; positive characteristic and imperfect F. For SL_2/B = P^1,
the affine line complement is one reduced geometric point and its dual ideal is O(1),
checking the sign of the chosen Picard generator. The empty scheme cannot accidentally
satisfy the quotient hypotheses, because H has its identity section and q is surjective.

Searches actually run:

- msearch leanfinder, “The Picard group of a split flag variety has a basis of Schubert
  boundary divisors preserved by field extension”: eight hits, all linear-algebra or
  root-system bases, no scheme statement.
- msearch loogle, `"Picard", "Scheme"`: zero hits.
- msearch grep, `Schubert|Picard|IsBorel`, subdirectory AlgebraicGeometry:
  three elliptic-curve comments about ring Picard groups, no match.
- msearch leansearch, “The Picard group of a split flag variety is freely generated
  by its Schubert boundary divisors”: eight hits about CommRing.Pic; none is a flag
  scheme result.
- rg of WeilConjectures and Sheaf for Schubert, Bruhat, Borel, Picard, quotient,
  `split_flag_schubert_picard_lattice`, `BoundaryBasis`, and `divisorClass`:
  the existing Borel predicate is algebraically-closed-field-only; BruhatLongestCellCharts
  is also algebraically-closed-field-only and does not state this Picard result;
  AffineGroupPicardFieldInvariance mentions the needed result only in its proof docstring;
  the regular-space divisor dictionary and scheme Picard group were reused.
- grep of the exact item id in WeilConjectures: no match.
- rg of the three proposed fully qualified declaration tails in dag/lean_names_upstream.json:
  no match.
- tools/blueprint_refs.py search Borel and ancestor of the item were read while checking
  existing notions; no new node is introduced. The ancestor result is None, as on the item.

No STATEMENT-DISPUTED flag or source-based correction is needed. The outdated example
CompactObject.lean is now a withdrawn empty module; this delivery follows the current
module headers and explicit-universe conventions used by the active dependencies instead.

Validation: scompile.py compiled the complete module on the server in its sandbox and
library forms without errors or non-sorry warnings. The theorem is deliberately unproved.

## Second reading by Q127

Written by the maintainer's reviewer, because the delivered section only said that no
second reading took place (H11). The Lean and the records are unchanged.

Node statement as a list, with the Lean and the verdict for each item:

1. F any field: `{F : Type u} [Field F]`. No characteristic, perfection or closure
   assumption. Correct.
2. H reductive over F: `hH : ReductiveTorusCentralizer.IsReductive H`, the recorded
   def-sfb-reductive-torus-centralizer-terminology (affine, finite type, smooth,
   connected over the algebraic closure, no nontrivial connected normal unipotent
   subgroup over the closure). Correct.
3. T split maximal torus: `iT` with `hT : IsMaximalTorus iT` (closed, IsTorus, maximal
   among closed tori), and `hsplit : ∃ r, Nonempty (T ≅ splitTorus F r)`, an isomorphism
   of groups that includes r = 0. Correct.
4. B ⊇ T a Borel subgroup: `iB` with `hB` (closed subgroup, smooth, connected,
   IsSolvable from def-sfb-solvable-group-structure, and maximality: every factorization
   through a closed smooth connected solvable C is an iso), together with `jT` and `hjT`.
   The node's maximality also quantifies over non-smooth connected solvable subgroups.
   The Lean tests only smooth ones (Milne's Borel definition), so its hypothesis is
   weaker and the statement is at least as strong. It is still true. B_{F̄} lies in a
   Borel containing T_{F̄}. That Borel is defined over F because T is split, so the
   maximality over F forces B_{F̄} to be that Borel. IsBorelGroupScheme needs
   [IsAlgClosed F], so expanding the definition inline is right. Correct.
5. B split solvable: `hBsplit : IsSplitSolvable B` (def-sfb-split-solvable-right-torsors,
   G_a/G_m quotients). Correct.
6. Q = H/B as the represented fppf quotient: `q : H.X ⟶ Q` over F, flat, surjective,
   locally of finite presentation, and `IsPullback fst (fst * (snd ≫ iB)) q q`, so that
   H × B ≅ H ×_Q H by (h,b) ↦ (h,hb). The landed lem-sfb-split-reductive-characteristic-
   sequence (QuotientGeometry) and lem-sfb-reductive-borel-pair-structure use the same
   presentation. IsFppfQuotient needs a group homomorphism, which does not apply here
   because B is not normal. Correct.
7. Pic and pullback: `Scheme.Pic` with its CommGroup (tensor product; the inverse is the
   dual) and `Scheme.Pic.mapHom`. They agree on isomorphism classes with the node's
   inline definition.
8. ∃ d s, an open immersion j : A^d_F → Q with dense image: `j` is a morphism of
   Over (Spec F) out of `AffineSpace (ULift (Fin d)) (Spec F)`, and `BoundaryBasis`
   begins with `IsOpenImmersion j.left ∧ DenseRange j.left`. Correct.
9. Geometrically integral effective Cartier D_i: `D : Fin s → Q.left.IdealSheafData`,
   `hD i : (D i).IsInvertible` (locally regular principal, def-nagata-effective-cartier-
   ideal), and `GeometricallyIntegral ((D i).subschemeι ≫ Q.hom)` (integral, hence
   nonempty, after every field extension). Correct.
10. The supports are the distinct codimension-one components of Q ∖ j(A^d): injectivity
    of `i ↦ (D i).support`, plus the ∀ Z equivalence with images of `irreducibleComponents`
    of the complement subtype whose generic-point stalks have ringKrullDim 1. These
    components are closed and irreducible in a scheme, so they have generic points and
    the condition is not vacuous. Correct.
11. O_Q(D_i) = I_{D_i}^∨ and the map Z^s → Pic(Q) is an iso: `divisorClass` is
    `Pic.ofIsInvertible I.toModulesᵛ`, and there is `∃ e : Multiplicative (Fin s → ℤ) ≃*
    Q.left.Pic` with its value on every m, ∏ divisorClass^{m_i}. Negative powers are
    inverses, that is, duals. Correct.
12. For every extension L/F: the conclusion quantifies `∀ L : Type u` and gives
    `BoundaryBasis` for (Over.pullback p).obj Q, the pulled-back cell
    `(Over.pullback p).map j`, the same s, and the actual base changes
    `(D i).comap (pullback.fst Q.hom p)`. Mathlib's comap is the kernel of the base-changed
    closed subscheme, so these are the actual base changes and not new choices. It also
    gives `Pic.mapHom p_Q (divisorClass D_i) = divisorClass D_{i,L}`. Correct. L sits in
    the scheme universe, as in the landed characteristic-sequence item.
13. H = T and H = 1: `IsIso iT → d = 0 ∧ s = 0 ∧ Nonempty (Q ≅ Over.mk (𝟙 _))`. Since
    B = T, Q is Spec F, and the dense cell forces d = 0 and s = 0. Correct.

Edge cases: rank 0 and the trivial group (item 13); s = 0, where the empty product and
Multiplicative (Fin 0 → ℤ) trivial ≃ Pic(Spec F) = 1; d = 0; L = F; imperfect F with
inseparable or transcendental L (no restriction on L); negative exponents. The empty Q
is excluded because q is surjective and H has a section. For SL_2/B = P^1 the boundary
is a point and the generator is O(1) = I^∨, so the sign is right.

Searches: rg in Sheaf/WeilConjectures for IsBorel, coset quotient presentations, Schubert,
Picard basis and SplitFlagSchubert. The only Borel predicate is the algebraically closed
IsBorelGroupScheme. The recorded quotient presentation is the one above. There is no
existing statement of this Picard basis.

Gates: divisorClass and BoundaryBasis carry real data and source/blueprint docstrings,
the theorem is `by sorry` with the six node steps (step 3 in the post-FIX form) in its
docstring, `lean.statement` is verbatim the file signature, and only the item's `lean`
field changed.

Advisory: Scheme.Pic belongs to def-sc-picard-group, which is not a stmt_dep. The node
defines Pic inline, so this is a maintainer note only.

Mismatches found: none in the Lean or the records. Changed: this section only.
