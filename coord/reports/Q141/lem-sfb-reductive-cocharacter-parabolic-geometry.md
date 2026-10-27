## Worker report

The module `Sheaf.AlgebraicGeometry.GroupScheme.ReductiveCocharacterParabolicGeometry`
states `AlgebraicGeometry.ReductiveCocharacter.reductive_cocharacter_parabolic_geometry`,
with `sorry`, and supplies four transparent Prop-valued packaging definitions:
`LimitGeometry`, `SemidirectGeometry`, `QuotientGeometry`, and `IsRegular`.
No object is chosen from a postponed existence theorem, and no proof is supplied.
The node's statement and proof remain unchanged.

Sources read: Milne, Algebraic Groups (2017), Theorem 13.33 and proof, printed
pp.265--266; Proposition 17.60 and proof, p.372; Proposition 21.29 and proof,
pp.433--434; Theorem 25.1, p.544. The group-scheme, reductivity, torus, unipotence,
projectivity, orbit-extension and weight declarations were read in their recorded
source files. The local CompactObject example is withdrawn and contains no declarations;
this module follows the current module/public-section convention in brief-stage2 §3.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The field is `{k : Type u} [Field k]`. `G : Grp (Over (Spec (.of k)))`
  is an actual group scheme, with the recorded group objects and homomorphisms.
  `hG : ReductiveTorusCentralizer.IsReductive G` is exactly the dependency's
  smooth affine finite-type, geometrically connected reductive-group predicate.
  It includes geometric absence of smooth connected normal unipotent subgroups.
  `lam : Grp.mk (StandardGroupSchemes.multiplicative k) ⟶ G` is the cocharacter.
- For every `A : CommAlgCat.{u} k`, the three equivalences in `LimitGeometry`
  identify the image of each closed inclusion with the recorded
  `CocharacterLimit.parabolicPoints`, `unipotentPoints`, and `centralizerPoints`.
  Their definitions use the actual polynomial-to-Laurent open immersion and
  scheme morphisms on A¹, the zero section, and all algebra extensions and
  multiplicative-group points respectively. No reduced or field-only test is used.
- The three `IsClosedSubgroupScheme` clauses specify the represented closed
  subgroup schemes. `Smooth` and `GeometricallyConnected` are required for all
  three structure maps, including geometric nonemptiness.
- `jU ≫ iP = iU` and `jZ ≫ iP = iZ` fix the inclusions into P. Normality is
  `IsNormalSubgroupScheme jU.hom.hom`. The equation `jZ ≫ r = 𝟙 Z` says that
  r is a retraction; r is a group-scheme homomorphism because its type is `P ⟶ Z`.
  The `IsPullback` square with the identity section identifies U with its
  scheme-theoretic kernel. The final universal clause of `LimitGeometry`
  fixes r as evaluation at zero of every extended orbit; it is not an arbitrary
  splitting of the subgroup sequence.
- `SemidirectGeometry` gives an actual isomorphism `U.X ⊗ Z.X ≅ P.X`, whose
  forward map is multiplication of the two specified inclusions. Its action c
  is pinned by the conjugation formula. The displayed all-algebra multiplication
  equation is `(u,z)(v,w)=(u*(z*v*z⁻¹),z*w)` in the given group operations.
- Unipotence is the recorded `SolvableGroupStructure.IsUnipotent U`, including
  smoothness and a faithful closed finite-dimensional representation with
  nilpotent matrix difference from the identity on all geometric points.
  `(∃ n : ℕ, SplitUnipotentLength U n)` is the recorded finite smooth connected
  closed normal series with actual fppf G_a quotients. Length zero is allowed.
- `X : Over (Spec (.of k))` and `q : G.X ⟶ X` are the quotient and projection.
  `QuotientGeometry` requires `Smooth X.hom`, `IsProjective X.hom`, and
  `GeometricallyIntegral X.hom`. Projectivity is precisely the recorded closed
  immersion into finite projective space, not merely properness.
- On q, `Smooth`, `Surjective`, and `LocallyOfFinitePresentation` together with
  `QuasiCompact` and `QuasiSeparated` express smooth surjective finite presentation.
  `GeometricallyIntegral q.left` expresses integral nonempty geometric fibres;
  equivalently all residue-field extensions give integral nonempty fibres.
- The right-torsor is the `IsPullback` square with top arrow `fst G.X P.X`
  and left arrow `fst * (snd ≫ iP)`. Thus its comparison to the kernel pair is
  exactly `(g,p) ↦ (g,gp)`. Together with the fppf covering q, this says exactly
  that X represents the fppf sheafification of the right-coset presheaf: sections
  lift on the pullback of q, and two lifts differ by a unique P section.
  This uses the characterization of represented quotients already used by the
  recorded SolvableGroupStructure and SplitReductiveCharacteristic interfaces.
  It does not assert surjectivity on un-sheafified algebra-valued cosets.
- `GeometricallyIntegral G.X.hom` is the separate assertion about G itself.
- The universal `[Field L] [Algebra k L]` clause uses exactly the recorded
  `MultiplicativeType.baseChange` on groups, inclusions, and r, and the ordinary
  `Over.pullback` on X and q. `LimitGeometry` for these precise maps says the
  subgroups and evaluation retraction are the constructions over L.
  `QuotientGeometry` for the pulled-back q identifies X_L with the quotient over L.
  The isomorphism e identifies the standard G_m over L with the pullback of G_m
  over k, and its projection is fixed as Spec of the Laurent substitution
  `eval₂ (C.comp (algebraMap k L)) (unitOfInvertible (T 1))`. Hence e cannot be
  twisted by inversion or an unspecified automorphism. Representing-object and
  sheafification uniqueness make the comparisons canonical.
- The last universal clause introduces `T`, its inclusion `iT`, maximality,
  an actual split-torus isomorphism of some finite rank, a cocharacter nu,
  and `nu ≫ iT = lam`. `IsRegular iT nu` means every nontrivial character
  occurring in the adjoint tangent action has nontrivial composition with nu.
  For a split torus the composite is uniquely t ↦ t^n, so this is precisely
  n ≠ 0 as an integer. The existing character-weight definition is evaluated
  after algebraic closure, where the rational-point eigenspace definition is
  valid; over a finite ground field it must not be evaluated on its finite
  set of rational points alone. All characters of a split torus descend, so
  this geometric test is equivalent to the stated root condition over k.
  The action is fixed to conjugation; quantification over actions with that
  smul does not add an assumption, since the group action exists canonically.
  The conclusion `∃ e : T ≅ Z, e.hom ≫ iZ = iT` is equality as subgroup schemes
  inside G, retaining the inclusions, rather than an abstract isomorphism.

Recorded dependency declarations used:

- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`, bundled `Grp`.
- `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs`:
  `IsClosedSubgroupScheme`, `IsNormalSubgroupScheme`, and the kernel convention.
- `Sheaf.AlgebraicGeometry.ReductiveTorusCentralizerTerminology`:
  `ReductiveTorusCentralizer.IsReductive`, `.IsMaximalTorus`.
- `Sheaf.AlgebraicGeometry.SolvableGroupStructure`: `.IsUnipotent`;
  reductivity internally uses `.IsAlgebraic` and this same unipotence predicate.
- `Sheaf.AlgebraicGeometry.StandardGroupSchemes`: `.multiplicative`, `.additive`,
  `.affine`, `.map`, and their actual group structures.
- `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`: `.baseChange`, `.splitTorus`.
- `Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure`:
  `CocharacterLimit.IsOrbitExtension`, `.parabolicPoints`, `.unipotentPoints`,
  `.centralizerPoints`.
- `Sheaf.AlgebraicGeometry.GroupScheme.SplitUnipotentSeries`: `SplitUnipotentLength`.
- `Sheaf.AlgebraicGeometry.TorusCharacterTangentWeights`:
  `TorusCharacterTangent.weightSpace`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`: `IsProjective`.
- Mathlib's `Field`, `Algebra`, `Smooth`, `ConnectedSpace`, `GeometricallyConnected`,
  `LocallyOfFiniteType`, `QuasiCompact`, `GeometricallyIntegral`, `pullback`,
  `IsPullback` are reused with their published definitions.

The already-landed definition nodes for split additive series and character tangent
weights were added to stmt_deps. The new definition node
`def-sfb-cocharacter-limit-functors` records the four existing CocharacterLimit
definitions, and is the statement dependency for those notions. The theorem
`lem-sfb-cocharacter-limit-smooth-structure` remains only in proof_deps. No dependency
module repair is needed. All recorded proof-dependency modules are imported privately
unless already public statement imports. Mathlib matches are imported from their
recorded modules. Proof dependencies with no Lean declaration or Mathlib match
remain documented in the theorem's full eleven-step proof docstring; they are
not needed to type this statement and have no module to import yet.

Edge cases checked mathematically before writing: trivial lambda gives P=Z=G,
U=1 and X=Spec k; the additive series can have length zero. The trivial group,
rank-zero split torus, and empty root set are included. In a torus there are no
nontrivial adjoint weights, so the final clause gives Z=G=T. Positive characteristic
(including nonzero integer weights divisible by the characteristic) is retained:
regularity tests characters, not their differentials. Imperfect fields are permitted;
all connectedness assertions are geometric, not perfect-field shortcuts. Test
algebras include nilpotents and the zero algebra. The common universe u is the
established group-scheme and CommAlgCat convention and does not introduce a
smaller independent test-algebra universe.

Searches made:

- `msearch.py ... leanfinder "reductive algebraic group cocharacter parabolic split
  unipotent radical projective quotient"`: eight irrelevant Lie/root-system hits;
  no scheme-theoretic cocharacter geometry statement.
- `msearch.py ... loogle "GrpObj, IsProjective"`: zero hits; unknown identifier
  GrpObj in the remote Loogle index.
- `msearch.py ... grep "parabolic|Cocharacter|cocharacter"`: sixteen Mathlib hits
  about modular-form cusps and two-by-two matrices, none this statement.
- `rg -n "cocharacter|Cocharacter|parabolic|Parabolic" lean/WeilConjectures
  lean/Sheaf`: found the previously landed CocharacterLimit predicates and
  theorem over algebraically closed fields, and consumers; no exact theorem.
- `grep -rn "lem-sfb-reductive-cocharacter-parabolic-geometry"
  lean/WeilConjectures`: no result.
- `rg -n "ReductiveCocharacter|reductive_cocharacter_parabolic_geometry"` in
  Mathlib, WeilConjectures, Sheaf, and dag/lean_names_upstream.json: no clash.

No statement correction or STATEMENT-DISPUTED flag is needed. The initial compile
found a wrong guessed unit-constructor name; replacing it by Mathlib's actual
`unitOfInvertible` fixed it. Server scompile subsequently compiled both sandbox
and actual library-path versions cleanly in 4.6 seconds each. Final dry-run checks
are recorded by the delivery tool.

## Second reading by Q141

This is a second pass by the same dispatcher-started worker; no independent reader
was started, as the brief forbids other agents. The maintainer supplies independent
review. Reopening the node and source module, I checked each of the eleven clauses
above. In particular the retraction is fixed by evaluation, the semidirect law
retains the specified conjugation, the torsor square has right multiplication,
and the G_m scalar-extension comparison is fixed by its Laurent coordinate.
The geometric character test avoids the finite-field rational-weight problem.
All data in the helper definitions are explicit propositions about the specified
schemes and maps. The only `sorry` is the one named theorem matching the item.
No mismatch requiring a node correction was found.


## New nodes

`def-sfb-cocharacter-limit-functors` records the existing definitions
`AlgebraicGeometry.CocharacterLimit.IsOrbitExtension`, `.parabolicPoints`,
`.unipotentPoints`, and `.centralizerPoints` in
`Sheaf.AlgebraicGeometry.CocharacterLimitSmoothStructure`, lines 38--75.
Its `existing: true` record lists all four and copies the IsOrbitExtension
signature verbatim. No new Lean module or declaration is created. Milne
Definition 13.21, Proposition 13.24, and pp.263--264 define exactly these notions.
The orbit-extension equality is restriction along the polynomial-to-Laurent
open immersion. P is existence of the extension, U adds evaluation equal to
identity at zero, and Z tests all algebra maps and all multiplicative-group
points. The definitions require only a field and a group scheme, without any
of the smooth-connected structure theorem's hypotheses. The zero algebra,
nonreduced algebras, and trivial cocharacter are included.

Searches on this repair were logged with msearch.py: LeanSearch for
“cocharacter conjugation orbit extending to affine line parabolic unipotent
centralizer functors” returned eight unrelated matrix-parabolic and abstract
centralizer hits; LeanFinder for “cocharacter parabolic functor algebra points
affine line orbit extension” returned eight affine-space/limit hits; grep for
`IsOrbitExtension|parabolicPoints|unipotentPoints|centralizerPoints` returned
zero Mathlib hits. Direct rg in WeilConjectures and Sheaf located the four exact
existing definitions. The DAG contains their names only in the structure
theorem's record and has no definition node for them. blueprint_refs.py search
“cocharacter limit” returned zero nodes, and its ancestor command returned null;
the new node retains that ancestor and the item's via chain prefixed by the item.

## Repair of returned delivery 8a616f7a8131

H2 (the sole returned point): added the requested definition node with an
existing:true Lean record listing all four plain definitions, replaced
`lem-sfb-cocharacter-limit-smooth-structure` in stmt_deps by
`def-sfb-cocharacter-limit-functors`, and retained the theorem in proof_deps.
The return confirms every mathematical clause and all other checks pass.
The Lean file is byte-identical to the retained returned delivery; its SHA256 is
`74c4c700379cb5e6034ee84f109ff098990f2b16fcb2fd8718821fa30b1e8fef`.
The current main node differs from the retained delivery only in lean and
stmt_deps; the repaired item takes all other fields from current main.
The wrapper creates the new delivery commit on the current live branch.

Second pass on the repair: I read the new node alongside the four full
definitions and checked each quantified algebra, extension, orbit restriction,
zero value and universal commutation condition. None uses the theorem. The
item's mathematical statement, proof, proof_deps, and Lean remain unchanged.
