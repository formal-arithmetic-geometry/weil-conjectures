## Worker report

Q29, stage 2, 2026-10-18. The module
`Sheaf.Paper.FiniteFieldInternalHomFiniteness` states
`AlgebraicGeometry.ProEtale.finiteField_constantModel_internalHom` with proof `sorry`.
It uses the existing ambient module-object derived category, ambient internal Hom and
finite constant scalar model constructibility. No mathematical statement or DAG dependency
is changed, no new node is introduced, and no dependency record is repaired.

The three coefficient helpers are constituents of this statement's specified coefficient:
`finiteFieldCondensedRing` applies the recorded universe-polymorphic continuous-map
construction to A with the bottom (discrete) topology;
`finiteFieldCondensedRingMonObj` supplies its existing pointwise ring structure;
`finiteFieldCondensedRingComm` supplies the existing commutativity proof. None has postponed
data or a new assertion with `sorry`. These are coefficient specializations, not independent
notions or new definitions of constructibility or derived Hom.

Hypothesis-by-hypothesis and clause-by-clause rendering:

- Prime ell: `(l : ℕ) [Fact l.Prime]`.
- Arbitrary field k: `(k : Type u) [Field k]`.
- Positive characteristic p: `[Fact (ringChar k).Prime]`. For a field, positive
  characteristic is prime; conversely this hypothesis forces positive characteristic.
  Thus p is represented canonically by `ringChar k`, with no extra choice of p.
- p different from ell: `[Fact (ringChar k ≠ l)]`.
- Finite coefficient field A of characteristic ell: `(A : Type u) [Field A] [Finite A]
  [CharP A l]`. No cardinality, chosen basis, enumeration, or prime-field restriction.
- The discrete topology on A is constructed in `finiteFieldCondensedRing` as
  `letI : TopologicalSpace A := ⊥`; topology is not an additional hypothesis.
  Its sections are exactly the recorded continuous functions with pointwise operations.
- The condensed ring underline A is `finiteFieldCondensedRing A`. It calls
  `Profinite.continuousMapRingObjOfUniverse.{u,u} A` directly, with the recorded canonical
  `MonObj` and `IsCommMonObj`, not arbitrary supplied ring-object structures.
- X is a scheme over k: `(X : Scheme.{u}) [X.Over (Spec (.of k))]`.
- Separated: `[IsSeparated (X ↘ Spec (.of k))]`.
- Finite type: `[LocallyOfFiniteType (X ↘ Spec (.of k))]` and
  `[QuasiCompact (X ↘ Spec (.of k))]`, the standard finite-type conjunction.
- The coefficient sheaf A_X is
  `condensedRingObj (finiteFieldCondensedRing A) X`, literally the recorded p_X^*.
  Its equivalence with the constant sheaf is explained in proof step 1; it is not
  substituted by an unrelated coefficient sheaf or assumed as extra data.
- P and Q are arbitrary objects of `DerivedCategory (Mod (Sheaf
  (Scheme.ProEt.topology X) Ab.{u+1}) (condensedRingObj ... X))`. These are the ambient
  derived complexes of modules over that ring object, not a perfect subcategory or
  objects with a supplied local free resolution.
- Each input vanishes outside some finite cohomological interval, and all its cohomology
  sheaves have the specified finite constant models: `hP` and `hQ`, respectively, assert
  `constantModelBoundedConstructible (finiteFieldCondensedRing A) X` of the object.
  The predicate is the existing conjunction of t-structure boundedness and
  `∀ n : ℤ, IsConstantModelConstructible ... ((DerivedCategory.homologyFunctor _ n).obj K)`.
  Its finite-stratification branch applies since X is finite type over a field, hence qcqs.
  `HasFiniteConstantLocalModel` uses a finite presentation on the point before pullback;
  over the finite field its scalar values are precisely finite-dimensional vector spaces.
- The conclusion applies this SAME predicate to
  `((CondensedRing.derivedHom ... X).obj (op P)).obj Q`: it asserts both a finite
  vanishing interval and constructibility of every cohomology sheaf with the SAME model
  convention. This is the ambient Layer-B relative derived internal Hom, not global Hom
  groups and not a separately defined restricted Hom.
- There is no hypothesis that k is finite, perfect, separably closed, algebraically closed,
  or of bounded absolute Galois cohomological dimension. There is no extra finite-Tor,
  site-perfectness, dimension bound, or fixed output interval requirement.

Recorded statement dependencies opened and used:

1. `sk-def-sfb-dc-setting`: read the current recorded module
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`,
   including its source obtained through `scompile.py --source`. Its current
   `compactificationOverField` uses objects of `Over (Spec (.of k))` and the separated
   finite-type binders. The present theorem uses the equivalent unbundled `X.Over`
   binders; no compactification is needed in its signature. The module is publicly imported.
2. `sk-def-sfb-condensed-ring`: `Sheaf.Topology.ContinuousMapCondensedRing`,
   `Profinite.continuousMapRingObjOfUniverse`, its `...MonObj` and
   `isCommMonObj_continuousMapRingObjOfUniverse`. Read each full declaration and docstring.
   Our coefficient helpers are these exact constructions with discrete A and universe u.
3. `sk-def-sfb-pulled-back-coefficients`:
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic`,
   `AlgebraicGeometry.ProEtale.coefficientRing`, `coefficientRing_X`, `condensedRingObj`
   and `isCommMonObj_condensedRingObj`. Read the source signatures and their monoidal
   pullback descriptions; `condensedRingObj` is exactly the underlying coefficient sheaf.
4. `sk-def-sfb-constructible`: `Sheaf.Paper.CondensedConstantConstructibility`,
   `HasFiniteConstantLocalModel`, `IsFiniteConstantStratified`,
   `IsConstantModelConstructible`, and `constantModelBoundedConstructible`.
   The full file was read. No copy of these predicates is made.
5. `sk-def-sfb-derived-tensor-hom`:
   `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom`,
   `AlgebraicGeometry.ProEtale.CondensedRing.derivedHom` and its unary and parameter
   adjunctions. The full module was read: the Hom is the internal Hom of the K-flat
   relative derived tensor. The conclusion invokes this recorded definition directly.

The proof docstring renders all eleven current DAG steps, naming the weak-Serre,
exact inverse-image, finite-type direct-image, support-triangle, tensor sheafification,
flat-generator, truncation-triangle, local-Hom and stratum-Hom inputs. The published modules
of all non-Mathlib proof dependencies are imported non-publicly (duplicates already publicly
imported are omitted). Mathlib's noetherianity, immersion, qcqs permanence, exact
sheafification and exact-cohomology ingredients are available through these imports.
No proof is attempted at stage 2.

Source and edge cases:

I opened the actual Bhatt--Scholze PDF via a sandbox-only pdftotext extraction and read
Lemma 6.7.13, its use of 6.7.11, Definition 6.5.1 and Lemma 6.3.16. With R=A and m=0,
completion is trivial and constructible coefficients are finite-dimensional. The cited
result is about internal sheaf Hom, so no field cohomological-dimension hypothesis is
needed. I also opened the current main-20261015 ancestor statement
`sk-def-sfb-dc-restricted-functors/lem-sfb-dc-hom-preserves.md`.

Checked before writing: X empty; P=0 or Q=0; zero-dimensional local models; complexes
concentrated in any shifted degree; distinct input bounding intervals; X=Spec k with k
imperfect or of large absolute ell-cohomological dimension; arbitrary finite extensions
of the prime coefficient field. Empty strata and rank zero are permitted by the recorded
constructibility definition. Boundedness is existential separately for each input and
output; no sharp output range is asserted. p=ell is excluded exactly as in the node.
A zero ring is excluded precisely because A is a field, as the node requires.
All universes are explicit (`u`); the site has object universe u+1 and morphism universe u,
while abelian coefficient values have universe u+1. A finite field in Type u loses no
coefficient isomorphism class, and no site-universe equality is imposed.

Searches for an existing exact statement (all run through the prescribed wrapper):

- LeanFinder: "Bounded constructible complexes of finite field coefficient sheaves on a
  scheme are closed under derived internal Hom". Eight hits, concerning light-condensed
  monoidal closed structures, abelian categories and AB4; no geometric finiteness theorem.
- Loogle: `"derivedHom", "constructible"`. Successful, zero hits.
- LeanSearch: "Derived internal Hom of bounded constructible finite field sheaves is bounded
  constructible". Eight hits, including `MonoidalClosed.internalHom`, `ihom`, sheafHom and
  Ext infrastructure, none asserting the result. Read the monoidal-closed source context.
- Mathlib grep: `(boundedConstructible|[Cc]onstructible).*(derivedHom|internalHom)|derivedHom.*[Cc]onstructible`.
  Successful, zero hits.
- rg in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures`, the shared `lean/Sheaf`,
  and `dag/lean_names_upstream.json`: the same conceptual pattern and the exact item id.
  Found etale stability results, the finite-geometric-field Hom comparison and the
  already recorded integral/finite-stage finiteness results. Opened
  `SixFunctors/Etale/Derived/Stability/DirectImage.lean` around
  `boundedConstructible_derivedHom`, and `ProEtale/Derived/HomComparison.lean` around
  `nonempty_iso_mapDerivedCategory_derivedHom`: they use etale categories/finite-Tor
  assumptions or an algebraic closure of a finite field. Opened
  `Sheaf.Paper.FiniteConstructibleHom`: its pro-etale theorem fixes the geometric base
  over an algebraic closure of a finite field and special positive-level coefficients.
  These are not exactly this statement in its recorded condensed module category.
- Exact names `finiteFieldCondensedRing` and `finiteField_constantModel_internalHom`
  were searched in Mathlib, both source roots and upstream-name records: no hits.

No STATEMENT-DISPUTED condition or node fault was found. The historical N5 stage-1 packet
was absent locally; its landed report was read, and the current stage-1 node is retained.
No stage-1 delivery command is needed for this stage-2 task.

## Worker final rereading

This is the worker's final rereading, not a claim of an independent second worker review.
The dispatch brief explicitly assigns independent review to the maintainer and prohibits
starting another agent. With the node and module open, I checked each hypothesis and clause
against the mapping above, especially the discrete topology, the exact scalar-model
predicate, the ambient internal Hom and the absence of assumptions on the ground field.
The three helpers merely install the existing canonical coefficient specialization.
The theorem has only `sorry`; helpers use existing actual data. No mismatch or statement
correction was found in this rereading. Compilation and dry-run results are recorded below.


## Compile repairs

The first compiler run found that installing the bottom topology alone does not register
its discreteness with typeclass inference. The helpers now use Mathlib's
`discreteTopology_bot A`, and the module publicly imports
`Mathlib.Topology.Algebra.Ring.Basic` for `DiscreteTopology.topologicalRing`.
The proposition-valued commutativity instance uses `let` in place of `letI` as requested by
the style linter. These are implementation repairs to the fixed discrete-topology
construction, with no change to the theorem signature, hypotheses or conclusion.

The next compiler diagnostic showed that Mathlib scopes the canonical monoid-object
structure of a functor image under `CategoryTheory.Obj` (Monoidal/Mon.lean:838).
Opening that existing scope enables exactly the recorded strong-monoidal pullback
structure on A_X. It introduces no notation, helper construction or mathematical assumption.


## Validation

The final `scompile.py Q29 lem-sfb-finite-field-internal-hom-finiteness` run passed
both the sandbox check and compilation under the final module name, with no warnings.
The prescribed `deliver2.py Q29 lem-sfb-finite-field-internal-hom-finiteness --no-push`
then printed `OK (dry run): commit 84e82b99a5 passes the preflight and compiles; nothing pushed`.
Only the item node record, its one Lean module and this report are in the delivery.
The node copy was checked against the shared node: only `lean` differs; every Lean line
is at most 100 characters. The final delivery wrapper rechecks the complete packet.

## Second reading by Q29

Independent maintainer second reading, 2026-10-18, of immutable delivery
c1441a8c106b4284fe2b471ffc57ac69d396289a. This reading was performed by a reader
who neither wrote nor previously second-read the delivery. The original placeholder
under this heading has been replaced by this actual reading; no worker review is invented.

I read the item node, all five statement-dependency nodes in the immutable snapshot,
the delivered module and its complete docstrings, the worker report, and the exact
coefficient, constructibility and derived-Hom declarations in the read-only group
framework. The three delivered files were byte-compared with the named commit.
Only the item's lean record is added; its mathematical statement, proof and dependencies
are unchanged. The lean.statement field equals the theorem signature verbatim.

Source: the actual Bhatt--Scholze PDF, Lemma 6.7.13 (printed p. 57), its preceding
Lemma 6.7.11, Definition 6.5.1 (p. 49), and Lemma 6.3.16 (p. 48). I also read the
blueprint ancestor lem-sfb-dc-hom-preserves and its proof, specifically the finite
coefficient sentence following reduction modulo varpi. Taking R=A, m=0 makes
completion trivial. For field coefficients the perfect local values in the source
are exactly bounded finite-dimensional values. A finite-type scheme over a field is
Noetherian and quasi-excellent, and p != ell gives ell-invertibility. The source is
about internal sheaf Hom, so it needs no bound on the absolute Galois cohomological
dimension of k. The node requests the first conclusion of 6.7.13, not its separate
coefficient-change conclusion.

Hypotheses and conclusions checked against the Lean:

- ell prime is l with Fact l.Prime. k is an arbitrary Field. Fact (ringChar k).Prime
  means positive characteristic for a field, with p its canonical ringChar; the next
  Fact is exactly p != ell. No finiteness, perfection or separable-closedness is assumed.
- A has Field, Finite and CharP A l. It is an arbitrary finite extension of the prime
  field, with no chosen basis. finiteFieldCondensedRing installs the discrete bottom
  topology and invokes continuousMapRingObjOfUniverse. Its MonObj and commutativity
  instances use the canonical recorded pointwise structures. All three bodies contain
  actual data or existing proofs, with no sorry or arbitrary choice of a ring structure.
- X is Scheme.{u} over Spec k, with IsSeparated, LocallyOfFiniteType and QuasiCompact
  on its structure map: exactly separated finite type. No compactification is supplied
  as an extra hypothesis. The setting dependency is used through these explicit binders.
- The coefficient is literally condensedRingObj (finiteFieldCondensedRing A) X,
  namely (upperStarFromPoint X).obj of the recorded continuous-map condensed ring.
  The strong monoidal pullback gives its ring structure. Discrete continuous functions
  are locally constant functions, so this is the stated constant coefficient sheaf.
- P and Q range over the full ordinary DerivedCategory of internal module objects.
  hP and hQ use constantModelBoundedConstructible. I unfolded that predicate: it is
  t-structure boundedness together with IsConstantModelConstructible of every integer
  homology sheaf. Finite-type X is qcqs, so the finite global stratification branch
  applies. Scheme.Stratification includes constructible locally closed disjoint strata
  covering X. HasFiniteConstantLocalModel pulls back a globally finitely presented
  condensed module from the point. Mod.IsFinitelyPresented means a cokernel of a map
  between finite sums of the regular module. Those maps are finite scalar matrices;
  for discrete finite A their cokernels are precisely finite-dimensional constant models.
  It does not silently use arbitrary local presentation matrices on X.
- The result applies exactly the same predicate to
  ((CondensedRing.derivedHom ... X).obj (op P)).obj Q. I read derivedHom: it is
  MonoidalClosed.internalHom for the relative K-flat derived tensor on Mod_{A_X},
  with its parameter and unary adjunctions. Hence both boundedness and all constructible
  cohomology clauses concern the ambient internal Hom, with the correct variance.
  There is no added perfectness, finite-Tor, site-perfectness or fixed-interval hypothesis.

Dependency interfaces read: ContinuousMapCondensedRing (continuousMapRingObjOfUniverse,
its MonObj and commutativity theorem); ModuleObject.Basic (upperStarFromPoint,
coefficientRing, coefficientRing_X, condensedRingObj and its commutativity instance);
CondensedConstantConstructibility (all seven recorded predicates/subcategories);
ModuleObject.Derived.Hom (derivedHom and both adjunctions), with Derived.Tensor and
ModuleObjects.DerivedCategory for the relative K-flat structure; and the setting module
ModuleObject.Derived.BoundedConstructible. The setting's older constructibility notation
is not substituted for the node's finite constant model predicate.

The proof docstring follows all eleven node steps: constant coefficients and Noetherian
geometry; weak-Serre and finite stratification gluing; bounded triangle closure; exact
pullback; finite-type direct-image finiteness through etale origins and comparison;
closed support; flatness over a field; sheaf and truncation devissage; local finite-free
Hom calculation; the open-then-closed generator Hom calculation; and contravariant
triangle induction. In particular it keeps ambient Hom, the order g_* j_!, and arbitrary
k. All four declarations have source-place and blueprint docstrings. The only theorem
body in the delivery is sorry; no mathematical proof was added locally.

One-definition check: I independently searched the project and Mathlib source trees for
internal/derived Hom constructibility and the exact new names. I opened the nearby
Etale.boundedConstructible_derivedHom, ProEtale.DerivedCategory's
nonempty_iso_mapDerivedCategory_derivedHom, and Sheaf.Paper.FiniteConstructibleHom.
They concern a different etale/finite-coefficient category, finite-Tor hypotheses,
geometric finite-field bases or specialized level coefficients; none is the present
ambient module-object assertion over arbitrary k. The worker also records actual
LeanFinder, Loogle, LeanSearch and grep searches. The three new helpers merely specialize
the recorded continuous-map construction, not a second coefficient or Hom theory.

Edge cases checked: empty X and empty stratification, zero P or Q, zero-rank models,
complexes in arbitrary shifted degrees and different finite input intervals, arbitrary
finite coefficient field extensions, imperfect k and k of unbounded Galois cohomological
dimension. p=ell and zero A are excluded exactly by the node's hypotheses. The output
interval is existential, with no uniform bound asserted. autoImplicit is false; u is
bound, and Scheme.ProEt retains object universe u+1 and morphism universe u with
Ab.{u+1} values. Putting the finite coefficient field in Type u loses no finite-field
isomorphism class; there is no equality imposed between the site's two universes.

Route-pivot check: none of the item's statement or proof dependency IDs occurs in
coord/route-pivot-dropped.txt from origin/newtargets-dag. The item's repair note is a
resolved stage-1 re-splitting note, not a route-pivot note. Neither the statement nor
its eleven-step proof reintroduces enhanced localizations, dg/infinity machinery,
Quillen rectification, coherent sections or operads. This is the ordinary derived route.

Reproducibility: ran scompile.py Q29 lem-sfb-finite-field-internal-hom-finiteness on the
immutable snapshot's sole Lean file. Exit code 0, no warnings or errors: sandbox
Sheaf/Stage2/Sandbox0.lean 6.6 seconds; final library module 9.6 seconds, with the
sandbox overlay under /dev/shm/nt-tmp/nt-local-compile-w0_aff3v/.lbuild. The installed
scompile.py sends the prescribed per-file overlay job to the server; I used that
wrapper, not a direct SSH command or a local/global lake build. This independently
confirms the worker's recorded successful per-file compile. No live Lean or clone was
edited, no delivery or landing was run, and no branch head was changed.

Finding and repair: H11 (and the substantive report requirement of H1): the original
Second reading by Q29 section explicitly said no second reading occurred. The complete
replacement report preserves the Worker report and replaces that placeholder with this
independent clause-by-clause reading and compiler evidence. No mathematical, Lean,
node-record, universe or dependency repair is needed. Verdict: FIX, report only.
