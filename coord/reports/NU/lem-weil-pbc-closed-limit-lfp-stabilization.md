## Worker report

The module `Sheaf.AlgebraicGeometry.ClosedLimitLfpStabilization` states
`AlgebraicGeometry.exists_isIso_limitProjection_of_isClosedImmersion_of_locallyOfFinitePresentation`
with `sorry`. It introduces no definitions and changes only the item's `lean` record.
The source is Stacks Project, limits.tex, lemma-finite-type-eventually-closed, Tag 081B(3),
applied with Y equal to the limit and the identity map. I read the source statement and proof.

Clause-by-clause correspondence:

- The base scheme is `S : Scheme.{u}`.
- The nonempty directed set is `{I : Type u} [Preorder I]
  [IsDirected I (· ≤ ·)] [Nonempty I]`, using the required preorder convention.
- The inverse system is `D : Iᵒᵖ ⥤ Scheme.{u}`. Its functor identity and composition
  laws give the inverse-system laws. The stage U_i is `D.obj (op i)` and r_ji is
  `D.map (homOfLE h).op` for h : i ≤ j.
- The structure maps q_i and their compatibility are the natural transformation
  `t : D ⟶ (Functor.const Iᵒᵖ).obj S`: naturality reads
  `D.map f ≫ t.app j = t.app i`, exactly q_j = q_i ∘ r_ji with the opposite indices.
- Quasi-compactness of every stage is `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`.
  This is quasi-compactness of the underlying space, with no Hausdorff requirement.
- Local finite type of each q_i is `[∀ i : Iᵒᵖ, LocallyOfFiniteType (t.app i)]`.
- Closed immersion transitions are
  `[∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsClosedImmersion (D.map f)]`.
  Affineness follows from Mathlib's existing closed-immersion instance; it is not a
  separate assumption. Including identity transitions adds no condition, since identities
  are closed immersions.
- The given inverse limit and projections are `c : Cone D` and `hc : IsLimit c`,
  with vertex `c.pt` and projections `c.π.app (op i)`. This uses exactly the Cone/IsLimit
  representation in the dependency `exists_limit_affine_transition`, not a new limit notion.
- The induced map to S is `q : c.pt ⟶ S` with
  `hq : ∀ i : Iᵒᵖ, c.π.app i ≫ t.app i = q`. This expresses the node's word
  "induced", not an added geometric hypothesis: the compatible composites agree on a
  nonempty directed system, and specify the induced map uniquely.
- Local finite presentation of q is `[LocallyOfFinitePresentation q]`.
- The entire conclusion is `∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsIso (c.π.app (op i))`:
  every projection at or beyond one common bound is an isomorphism.

Dependencies read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Morphisms.QuasiCompact`: `QuasiCompact` (the convention dependency distinguishes
  quasi-compact schemes from quasi-compact morphisms; here the former is CompactSpace).
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.
- `Mathlib.AlgebraicGeometry.Morphisms.Affine`: `IsAffineHom`, available through imports.
- `Sheaf.AlgebraicGeometry.LimitAffineTransition`: `exists_limit_affine_transition`;
  I read its full signature and docstring. The statement takes an arbitrary limiting cone,
  as supplied by this theorem, rather than choosing a second limit construction.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`: `LocallyOfFinitePresentation`
  and its `finitePresentation_appLE` field.
- `def-weil-pbc-scheme-conventions` has no declaration by design: its recorded conventions
  are implemented with the above Mathlib properties and `CompactSpace`.

The proof-only dependencies have no additional Sheaf modules to import. Their recorded
Mathlib declarations are imported: `Concrete.isColimit_exists_rep` and
`Concrete.isColimit_rep_eq_iff_exists` (Limits.ConcreteCategory.Basic), filtered-colimit
preservation for CommRingCat (Algebra.Category.Ring.FilteredColimits),
`Algebra.FinitePresentation.ker_fg_of_mvPolynomial` (RingTheory.FinitePresentation),
`Scheme.Cover.glueMorphisms` and `Scheme.Cover.hom_ext` (AlgebraicGeometry.Gluing).
All theorem proofs in the delivered module are `sorry`; its docstring supplies all five
natural-language proof steps, including the finite-kernel and overlap-gluing details.

Edge cases: the index type cannot be empty, exactly as required. Singleton indices and
preorders with equivalent distinct indices are allowed. Empty stages, empty affine covers,
zero rings, and empty lists of kernel generators are allowed; the proof plan addresses
these without imposing nonemptiness of schemes or positivity of generator counts.
No quasi-separatedness, separatedness, Noetherian, or finite-presentation hypothesis on
the stages or base was added. Index and scheme universes share `u`, as required for limits.

Searches performed with msearch.py (NU, this item):

- LeanFinder: "A directed inverse system of quasi-compact schemes with closed immersion
  transitions and locally finitely presented limit is eventually isomorphic to the limit".
  Eight hits: hom-descent injectivity, eventual affine/quasi-affine results, compact-limit
  nonemptiness, and global-section descent. None states stabilization. I opened the closest
  hom-descent signatures and docstrings in Mathlib.AlgebraicGeometry.AffineTransitionLimit;
  they assert eventual equality of maps, not eventual invertibility of the projections.
- Loogle: `AlgebraicGeometry.IsClosedImmersion, AlgebraicGeometry.LocallyOfFinitePresentation,
  CategoryTheory.IsIso`. Zero hits.
- LeanSearch: "closed inverse system of schemes finitely presented limit eventually
  isomorphism". Service unavailable: Internal Server Error; no conclusion drawn from it.
- Mathlib grep: `eventually.*[Ii]so|[Ii]so.*[Ll]imit|stabili`, subdirectory
  AlgebraicGeometry. Twenty-five hits, on limit comparison isomorphisms and unrelated
  constructions, none this result.
- Direct rg in the source project's WeilConjectures, project lean/Sheaf, and upstream
  declaration index for `closed.limit|closed_limit|eventually.*[Ii]so|[Ii]so.*eventually|
  finite.type.eventually.closed`: only unrelated derived-limit and eventual-equality
  declarations. Direct grep for the exact item id in WeilConjectures: no hits.
- Broader direct rg for stabilization and eventual isomorphism likewise found unrelated
  stabilization topics; no duplicate declaration or definition was found.

No statement dispute, missing notion, unusable dependency, or correction was found.

Validation: scompile.py passed cleanly on the server (1.3 seconds, nice 19, two threads,
60 seconds per file). deliver2.py --no-push printed OK: compilation and preflight passed except for the
independent second-reading section, which the second reader will write. Nothing was pushed.

## Second reading by NU

I independently opened the item node, its five proof steps, the delivered Lean module,
all statement-dependency node records, the recorded LimitAffineTransition declaration,
and the Mathlib declarations below. I read limits.tex, lemma-finite-type-eventually-closed
(Tag 081B), its full hypotheses and proof of (3). This lemma is self-contained and is not
under Situation descent: there is no inherited quasi-separatedness assumption. Applying
(3) with Y = X and its identity gives exactly this node. No correction is necessary.

Object/hypothesis/conclusion checklist (each verdict: exact):

1. Base scheme S: `(S : Scheme.{u})`. Mathlib Scheme is a locally ringed space with local
   affine charts; Scheme.Hom is the morphism of locally ringed spaces. This is def-pc-scheme.
2. Nonempty directed set I: `{I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]`.
   The preorder convention agrees with the recorded limit dependency and includes posets.
3. Stages and transition maps: `(D : Iᵒᵖ ⥤ Scheme.{u})`, with U_i = D.obj (op i) and,
   for h : i ≤ j, r_ji = D.map (homOfLE h).op. Functor laws supply identity/composition.
4. Structure maps q_i to S and q_i composed with r_ji equals q_j:
   `(t : D ⟶ (Functor.const Iᵒᵖ).obj S)`. These are `t.app (op i)`; naturality is exactly
   the compatibility equation, with Lean composition written left-to-right.
5. Each stage quasi-compact: `[∀ i : Iᵒᵖ, CompactSpace (D.obj i)]`. This is compactness
   without a separation condition, hence quasi-compactness of the scheme itself; it does
   not assert quasi-compactness of the structure morphisms. The convention node adds no
   independent definition and the finite-type dependency distinguishes these notions.
6. Each q_i locally of finite type: `[∀ i : Iᵒᵖ, LocallyOfFiniteType (t.app i)]`.
   I read the class field finiteType_appLE in Morphisms/FiniteType.lean: finite type of
   induced maps on affine charts, the dependency's notion, with no finite-presentation
   or Noetherian hypothesis.
7. Closed immersion transitions: `[∀ {i j : Iᵒᵖ} (f : i ⟶ j),
   IsClosedImmersion (D.map f)]`. I read the class (closed embedding and surjective stalk
   maps) and its IsAffineHom instance in Morphisms/ClosedImmersion.lean. Affineness in the
   node is a consequence, not an additional hypothesis. The IsAffineHom class in
   Morphisms/Affine.lean means affine inverse images of affine opens, exactly the leaf.
8. Given limit U and projections: `(c : Cone D) (hc : IsLimit c)`, with U = c.pt and
   rho_i = c.π.app (op i). I read exists_limit_affine_transition in the project module,
   including its open-restriction and affine-comparison clauses. The delivered statement
   uses its actual Cone/IsLimit notion and works for any limiting cone, without requiring
   chosen affineness proofs or a chosen model for U.
9. Induced q : U → S: `(q : c.pt ⟶ S)` and
   `(hq : ∀ i : Iᵒᵖ, c.π.app i ≫ t.app i = q)`. This merely names the induced map.
   For any two indices a common upper bound, cone naturality and t.naturality equate
   the composites; nonemptiness supplies one composite defining q. Thus hq adds no
   geometric assumption. It also rules out applying finite presentation to an unrelated q.
10. q locally of finite presentation: `[LocallyOfFinitePresentation q]`. I read the
    finitePresentation_appLE field in Morphisms/FinitePresentation.lean. This is the
    recorded dependency, not globally finite presentation (no added quasi-separatedness).
11. One eventual bound and all subsequent projections isomorphisms:
    `∃ i₀ : I, ∀ i : I, i₀ ≤ i → IsIso (c.π.app (op i))`. Quantifier order, the actual
    projection morphisms, and the entire conclusion coincide with the node.

Edge cases: empty I is excluded by the node itself; singleton I and non-antisymmetric
preorders are permitted. Empty stages and empty limit schemes are permitted (CompactSpace
has no nonemptiness field). Zero rings and arbitrary characteristic are permitted because
there are no field or Nontrivial hypotheses. No natural number occurs in the statement;
the proof plan explicitly permits zero polynomial generators and an empty affine cover.
The sole universe u is declared, and index and schemes share it as the project requires;
there is no small test-object quantifier or unbound universe/variable. No separation,
quasi-separatedness, Noetherian or finiteness-of-index condition has been introduced.

Independent duplicate searches, using different wording from the first worker:

- LeanFinder via msearch.py: "inverse limit closed embeddings of schemes becomes stationary
  when the limit is of finite presentation". Eight hits: eventual equality of morphisms,
  nonempty limits, affine limits and affine space finite presentation. I opened the two
  exists_hom_comp_eq_comp / exists_hom_hom_comp_eq_comp_of_locallyOfFiniteType signatures
  and the latter's docstring in Mathlib's AffineTransitionLimit: these say eventual
  equality of maps, not invertibility of the projections. No matching declaration.
- Loogle via msearch.py: `AlgebraicGeometry.LocallyOfFinitePresentation,
  CategoryTheory.IsIso`. Zero hits.
- LeanSearch via msearch.py: "A projective system of closed subschemes locally of finite
  type stabilizes if its limit is locally finitely presented". Unavailable with Internal
  Server Error, recorded as unavailable, not evidence of absence.
- Direct rg in Mathlib AlgebraicGeometry, source WeilConjectures, project lean/Sheaf and
  dag/lean_names_upstream.json, using `stationar`, `stabili`, `exists_isIso`,
  `closed.limit|closed_limit|finite.type.eventually.closed|isIso_limitProjection` and
  eventual-isomorphism phrases. Hits were Noetherian chains, formal-module stabilization,
  derived-limit eventual isomorphisms and unrelated geometry. None states this result.

There are no new definition nodes or dependency modules in this delivery. The existing
Mathlib definitions and the project's limit declaration suffice; there is no private copy,
hollow definition, added helper theorem or proved theorem. I also read the proof-only
Mathlib declarations Concrete.isColimit_exists_rep, Concrete.isColimit_rep_eq_iff_exists,
CommRingCat.FilteredColimits.forget_preservesFilteredColimits,
Algebra.FinitePresentation.ker_fg_of_mvPolynomial and Scheme.Cover.glueMorphisms/hom_ext.
Their imported modules give the node's proof inputs. The module/declaration docstrings
name Tag 081B and the blueprint id; the proof docstring carries all five node steps,
including finite kernel generators, eventual vanishing and inverse gluing on overlaps.
The only theorem proof is sorry. The signature equals lean.statement verbatim, checked
mechanically, and all module lines are at most 100 characters.

Mismatches found: none. Changes: appended this independent second reading only; retained
both the correct Lean module and the node's lean record unchanged.
