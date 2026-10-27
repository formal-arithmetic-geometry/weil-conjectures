# Stage-2 delivery: free quotient Grassmannians

## Worker report

The delivery states `AlgebraicGeometry.exists_freeQuotientGrassmann_projective` in
`Sheaf.AlgebraicGeometry.FreeQuotientGrassmannProjective`. Its only theorem has proof
`sorry`. The helper `AlgebraicGeometry.freeQuotientPullback` has fully constructed data:
it is the coproduct map whose standard generators are sent to their images under the
section-normalized tensor-pullback unit. There is no existence choice of an object or
map, no private definition, no file-local notation, and no new axiom.

I read the current node, all nine original statement dependencies and their recorded
declarations, and the twelve-step proof. I read the quotient convention, equation
`gkn` (Tag 089S), and `lemma-gkn-representable` (Tag 089T) in
`literature/stacks-project/constructions.tex`, including the normalized quotient charts.
The rank in that text is n-k; the delivered statement uses r, so k=N-r in the interior
case. The projectivity completion is the current node's reviewed, explicitly
agent-written determinant-equation proof. I did not attribute that completion to the
unavailable Bourbaki archival PDF. The source statement is unchanged.

### Hypotheses and clauses

1. **Every base scheme.** `S : Scheme.{u}` and an explicitly declared arbitrary universe
   `u` permit every scheme in each fixed universe. The same universe is used for test
   schemes, so the universal property does not become vacuous through an undersized
   independent test universe. No affine, Noetherian, separated, reduced or field
   hypothesis is imposed.
2. **N nonnegative and 0 ≤ r ≤ N.** `N r : ℕ` and `hr : r ≤ N` state exactly these
   restrictions. No strict inequality is required for representability or projectivity.
3. **An S-scheme and universal quotient.** The existential binders `G`, `π : G ⟶ S`,
   `Q : G.Modules` and
   `q : SheafOfModules.free (R := G.ringCatSheaf) (ULift (Fin N)) ⟶ Q`
   introduce the representing scheme, its structural map and its actual universal
   quotient. The first two conjuncts, `Epi q` and `Q.IsFiniteLocallyFreeOfRank r`, say
   that the sheaf map is surjective and its target is Zariski locally O^r. Surjectivity
   here is sheaf surjectivity, not the stronger assertion that every sections map is
   surjective. `SheafOfModules.free` is Mathlib's coproduct of N copies of the unit
   sheaf, with its standard generators; it is not a second trivial-bundle definition.
4. **Every morphism pulls the universal quotient back to an allowed quotient.** The
   first universal conjunct gives `Epi (freeQuotientPullback a q)` and rank r for
   `(tensorPullback a).obj Q` for every `T` and `a : T ⟶ G`. This states that the
   proposed representing map takes its values in the required quotient classes.
5. **Representability of exactly the stated quotient functor.** For every `T`,
   `t : T ⟶ S`, `P : T.Modules`, and map `p : O_T^N ⟶ P`, the hypotheses are precisely
   `Epi p` and `P.IsFiniteLocallyFreeOfRank r`. The conclusion is
   `∃! a : T ⟶ G, a ≫ π = t ∧ ∃ e : (tensorPullback a).obj Q ≅ P,
   freeQuotientPullback a q ≫ e.hom = p`.
   Thus it classifies isomorphism classes of quotient pairs: the module isomorphism
   must preserve the quotient map. It does not classify bare locally free modules,
   subbundles, or arbitrary maps. Existence gives every quotient class; uniqueness
   gives injectivity on classes. Together with the preceding conjunct, this is the
   universal-element form of the representability definition recorded by
   `def-pc-representable-functor`. Naturality follows from composition of the recorded
   tensor pullback and uniqueness of the classifying map: applying pullback to a
   quotient-preserving isomorphism gives the composite's class. No representatives of
   a quotient set are chosen and no additional assumption replaces representability.
6. **Arbitrary base change of the scheme AND universal quotient.** For every
   `S' : Scheme.{u}` and `f : S' ⟶ S`, the next conjunct gives that same unique
   classification for the actual `pullback π f`, with structure map
   `pullback.snd π f`, target module `(tensorPullback (pullback.fst π f)).obj Q`,
   and quotient `freeQuotientPullback (pullback.fst π f) q`. The classifying equation
   uses the iterated pullback of this quotient, so it includes the universal quotient
   compatibility. Its rank and surjectivity follow directly from conjunct 4 applied
   to `pullback.fst π f`. This asserts that this base-changed scheme, equipped with
   this quotient, represents the same functor over S'. Yoneda's uniqueness gives the
   quotient-preserving isomorphism with a separately chosen representative over S'.
   There is no flatness restriction. Identity base changes and arbitrary test maps
   remain included.
7. **Endpoint ranks.** `(r = 0 ∨ r = N) → IsIso π` says precisely that G is S as an
   S-scheme. Since the representative is existentially bound, this invariant
   formulation is equivalent to choosing S itself; it does not merely assert an
   abstract isomorphism unrelated to the structure map. It includes N=r=0.
8. **Interior Plücker closed immersion.** The guards `0 < r → r < N →` are exactly
   the node's interior condition. The target
   `ℙ(ULift (Set.powersetCard (Fin N) r); S)` has homogeneous coordinates indexed by
   r-element subsets; `Set.powersetCard.card` identifies their number as N.choose r.
   This is P^(N.choose r - 1)_S with its natural subset labels. The existential map
   `j`, `IsClosedImmersion j`, and `j ≫ ... ↘ S = π` specify a closed immersion over S.
9. **The actual top-exterior-power construction.** The following isomorphism `e`
   identifies the tensor pullback of `ProjectiveSpace.twist ... S 1` with the recorded
   `Scheme.Modules.exteriorSheaf Q r`. For each subset I, the final equation sends
   the pulled-back `ProjectiveSpace.twistOneSection ... S I` to
   `exteriorSheafSection Q r ⊤` of the ordered quotient generators.
   `I.down.val.orderEmbOfFin I.down.property` enumerates I increasingly, fixing all
   signs. Evaluating `freeHomEquiv Q q` at `op ⊤` gives the image of the corresponding
   standard basis section. The left side uses the same normalized tensor-pullback
   adjunction as `freeQuotientPullback`. These equations identify the line quotient
   with the top wedge of q, rather than merely asserting some closed embedding into
   a projective space of the right size.
10. **H-projectivity in all cases.** The last conjunct is the existing
    `IsHProjective π`, outside the interior and endpoint implications. Hence it
    covers all allowed ranks, including both endpoints, as required.

### Dependency declarations and imports

- `def-pc-scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`,
  `Mathlib.AlgebraicGeometry.Scheme` (read definitions and local-affine docstring).
- `def-pc-representable-functor`: `CategoryTheory.Functor.RepresentableBy`, `yoneda`,
  `Functor.IsRepresentable`, `Mathlib.CategoryTheory.Yoneda`. The equivalent
  universal-element classification is expanded explicitly as explained above.
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, read lines 30–38:
  finite projective-space embedding with the structural-map equation.
- `def-weil-sheaf-of-modules-category`: the Mathlib category `SheafOfModules`, used
  by `Scheme.Modules`; `Sheaf.CategoryTheory.RingedSiteModules` transparently
  exposes the same category on general sites. No replacement category is constructed.
- `def-pc-module-pullback`: `Scheme.Modules.tensorPullback` and
  `tensorPullbackSectionAdjunction`,
  `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`. I read the functor and
  normalized-unit interface, including `tensorPullbackSectionComp` and
  `tensorPullbackSectionId`; the helper uses the unit on standard generators.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`, `pullback.fst`, and
  `pullback.snd`, `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  lines 95, 111, 115; the scheme instance comes through the projective-space import.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, lines 40–46.
- `def-nagata-projective-space-base-change`: `AlgebraicGeometry.ProjectiveSpace`
  and its structure morphism, `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`,
  read the construction and homogeneous-coordinate convention.
- `def-sc-sheaf-exterior-power`: `Scheme.Modules.exteriorSheaf` and
  `exteriorSheafSection`, `Sheaf.AlgebraicGeometry.Modules.ExteriorSheaf`. I read
  both local and live-server source with `scompile.py --source`; the delivered
  statement uses this exact recorded construction.
- Added existing statement dependency `def-amb-finite-locally-free-module`:
  `SheafOfModules.IsFiniteLocallyFreeOfRank`,
  `WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`, lines
  130–138. It is the existing constant-rank notion, including rank zero. Its
  specialization to a scheme says exactly locally O^r as the node requires.
- Added existing statement dependency `def-pc-projective-space-twist`:
  `AlgebraicGeometry.ProjectiveSpace.twist` and `twistOneSection`,
  `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, definitions at
  lines 111 and 229. This records the existing O(1) used to specify the Plücker map.
- The helper also uses the existing
  `Scheme.Modules.homOfGlobalSection` from
  `WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator`, whose full
  definition and section formula were read. It is used only to turn the constructed
  pulled-back generator sections into the canonical coproduct map.

The stated proof dependencies are imported privately: matrix adjugate/Cramer and
determinants; multivariable polynomials; algebra quotients; Proj standard opens;
scheme morphism gluing; upstream relative-Proj functoriality; upstream module
sheaf gluing; upstream exterior-sheaf comparison; the existing projective-space
functor-of-points statement; and Mathlib's free exterior-power basis. The public
imports provide the remaining proof dependencies (projective space, pullback,
closed-immersion base change, H-projectivity, Yoneda uniqueness, and exterior sheaves).
The relative-Proj source was also checked on the live server with `scompile.py
--source`, and only its graded-surjection clause is used by the natural-language
proof. Every one of the node's twelve proof steps is included in the theorem docstring.

### Edge cases

Checked N=0,r=0, r=0, r=N, and N=1 (only endpoint ranks); the classification and
base-change binders include them and the Plücker guard excludes them exactly as in
the node. For r=1 the subset coordinates give ordinary projective-space coordinates;
for N=3,r=2 they are the three increasing wedge pairs. For N=4,r=2 the six sections
have the standard Plücker signs. The ordered enumeration fixes signs also in
characteristic two. Empty schemes and the zero ring are allowed; constant rank r
on an empty scheme is vacuous and its only module quotient is still classified
correctly. No rank comparison on a nonexistent point is used. Nonreduced tests,
such as Spec(Z/4), are included because the quotient equations and isomorphisms
are scheme/module statements, not statements about geometric point sets.

### Searches

Actual search calls, group NU and this item, using the prescribed msearch wrapper:

- LeanFinder: `Grassmannian scheme represents locally free quotients of a trivial
  sheaf with Plucker projective embedding`: eight hits, principally
  `Module.Grassmannian`, `projective_quotient`, and `AlgebraicGeometry.Proj`.
- Loogle: `Grassmannian`: no hit, unknown unqualified identifier. This was not
  treated as evidence that the qualified construction is absent; the LeanFinder
  candidates were opened directly.
- Mathlib grep in `AlgebraicGeometry`: `Grassmann|Plucker|plucker`: zero hits.
- LeanSearch: `Grassmannian scheme represents finite locally free quotients of a
  trivial bundle`: eight hits, the module Grassmannian family only.
- Direct `rg` over both `lean/WeilConjectures` and `lean/Sheaf` for
  `Grassmann|grassmann|Plucker|plucker|FreeQuotient`, followed by the exact item id
  and proposed declaration names. No existing theorem or construction matched.
  A subsequently landed Hilbert-scheme docstring mentions this node as a proof
  prerequisite, not a statement of it.
- Opened `Mathlib/RingTheory/Grassmannian.lean`, especially lines 35–53: it explicitly
  lists scheme Grassmannians and representability as TODO. The module quotient being
  projective is not the representing scheme being H-projective.

No independent notion was absent: the one local helper is the actual canonical map
belonging to this node's universal-quotient statement, as authorized by the human's
helper-declaration rule. Its declaration is listed in `lean.declarations`. There
are no new nodes, no dependency repairs, no statement correction, and no
STATEMENT-DISPUTED finding. The earlier worker's stale-assignment diagnosis was
incorrect: NV supplied and reviewed the stage-1 split, but the current item has no
Lean record. This delivery supplies its stage-2 statement.

### Validation

`scompile.py NU lem-sfb-free-quotient-grassmann-projective` compiled the delivered
module in module mode both as a sandbox and under its library module name, with
no errors or unexpected warnings. The first compile found that Mathlib's
`freeHomEquiv` produces compatible section families, not sections over the top
open. I corrected the implementation to evaluate those families at `op ⊤` and
to use the existing global-section morphism when constructing the pullback map.
The corrected file compiles cleanly. Both implicit-binding options are disabled;
the universe, schemes, integers, module objects and morphisms are explicitly bound.
All lines have length at most 100. No library build or direct repository mutation
was performed.

## Second reading by NU

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
