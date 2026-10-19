## Worker report

The module `Sheaf.Algebra.Homology.SemidualizingRHomConservative` states
`DerivedCategory.semidualizing_rhom_conservative`, with one `sorry` proof and no new
definitions. Its conclusion is a conjunction of object detection and morphism detection.
The statement is unchanged mathematically. The node copy changes only `lean` and adds two
already recorded nodes to `stmt_deps`: `def-pc-ring-hom-extension-shared-definitions` and
`lem-weil-pbc-ringed-internal-hom-exact-restriction`.

Clause-by-clause rendering:

- Commutative Noetherian ring A: `(A : Type u) [CommRing A] [IsNoetherianRing A]`.
- Ordinary D(A): `DerivedCategory (RingSiteModules A)` with
  `[HasDerivedCategory.{u} (RingSiteModules A)]`. `RingSiteModules` is the existing module
  category on the discrete one-object site with bottom topology and constant ring A.
  Evaluation at `op ⟨PUnit.unit⟩` identifies it with ordinary A-modules: the only restriction
  is the identity and every presheaf is a sheaf. Thus this is precisely the one-object
  ringed-site encoding explicitly requested by the node, not a geometric specialization.
- Bounded cohomology of C: `hCbounded` gives integers a,b and `IsZero H^i(C)` whenever
  `i < a ∨ b < i`. Bounds are on cohomology, not on a chosen representative's terms.
- Finitely generated cohomology of C: `hCfinite` asserts `Module.Finite A` for every
  evaluated cohomology object. Evaluation on this site is exact, so these are the ordinary
  cohomology modules.
- The scalar-action morphism is an isomorphism: `hscalar` is `IsIso` of
  `(SignedRingedHom.adjunction ⊥ (CochainComplex.onePointRingSheaf A) C).homEquiv _ _
  (λ_ C).hom`. The imported adjunction is `tensorRight C ⊣ SignedRingedHom.hom ... C`.
  Its left argument is therefore `A ⊗^L C`, and the left unitor is scalar multiplication.
  The adjunction is uniquely normalized on K-flat representatives by ordinary evaluation;
  its transpose sends a to multiplication by a. Its source is the derived tensor unit A,
  and its target is RHom(C,C). No arbitrary arrow or assumed isomorphism is substituted.
- For every bounded finite-cohomology Z: the first conjunct quantifies over Z and gives
  exactly the same boundedness and `Module.Finite` premises, independently of C's bounds.
- RHom(C,Z)=0 implies Z=0: the remaining implication in the first conjunct is
  `IsZero ((SignedRingedHom.hom ... C).obj Z) → IsZero Z`. Equality to zero in a derived
  category means being a zero object; it does not demand literal equality of chosen objects.
- For every f:X→Y with X,Y bounded and finite-cohomology: the second conjunct universally
  quantifies X,Y,f and supplies separate boundedness and finiteness premises for each.
- If RHom(C,f) is an isomorphism then f is: its last implication is
  `IsIso ((SignedRingedHom.hom ... C).map f) → IsIso f`.
- No finite projective/injective dimension: neither premise appears. There is no local,
  complete, nonzero, domain, perfectness, or finite-Tor-dimension premise.

Dependencies read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, with the ideal-finiteness
  characterization `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`, `DerivedCategory`;
  `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: `homologyFunctor`.
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`:
  `CategoryTheory.derivedInternalHomOfUniverses`, the recorded definition of RHom by the
  Hom complex and functorial K-injective replacement, descended through localization.
- `Mathlib.RingTheory.Finiteness.Defs`: `Module.Finite`.
- `Sheaf.Algebra.Homology.RingHomExtensionDefs`: `CategoryTheory.RingSiteModules`, using
  the existing `CochainComplex.onePointRingSheaf` and unique evaluation object.
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`:
  `SignedRingedHom.hom`, `homFunctor`, `adjunction`, `derivedMonoidal`, and the normalization
  theorem `normalizedAdjunction_existsUnique`. In particular `homFunctor` is definitionally
  the above recorded `derivedInternalHomOfUniverses`, not an unrelated closed structure.

These two additional landed dependency IDs merely record the interfaces already in the
library that the statement uses. No dependency record was repaired and no definition node
was created. The module imports all currently recorded proof-dependency modules, privately
when only the proof uses them. The three proof dependencies
`lem-trf-pseudocoherent-rhom-flat-base-change`, `lem-trf-complete-local-coherent-duality`,
and `lem-trf-local-derived-tensor-nonvanishing` have no recorded Lean module at preparation
time, so no fabricated imports are inserted. Their full mathematical use remains in the
proof docstring. The maintainer can add their imports when they acquire modules.

Edge cases and source reading:

- A is allowed to be the zero ring. There is no `Nontrivial A`; all its module objects
  are zero, and both conclusions hold. The proof's maximal-localization step allows the
  empty set of maximal ideals.
- Zero C is not explicitly excluded. Over a nonzero ring hscalar rules it out; over the
  zero ring it is allowed. Zero Z,X,Y and f between zero objects are included.
- Bounds may be negative, positive, equal, or reversed. Reversed bounds describe zero
  cohomology, a legitimate case. X,Y,Z need not share an interval.
- Cohomology may be finite over a ring with infinite global dimension. The derived tensor
  in the complete-local proof may be unbounded below; no perfectness is introduced.
- The universe u is explicitly declared and arbitrary. The site category is
  `Discrete PUnit.{u+1} : Type u` with morphisms in u, so this encoding imposes no equality
  between originally independent site universes. The chosen Hom universe u is available
  for every such Grothendieck module category, as in the recorded signed calculus. This
  is a choice of size convention, not a condition on A or its complexes.
- Read `literature/stacks-project/dualizing.tex`, labels `lemma-dualizing` (Tag 0A7C) and
  `lemma-ubiquity-dualizing` (Tag 0BFR), using `tags/tags`. The former explicitly treats
  all coherent complexes and restricts to bounded coherent complexes; the latter supplies
  a dualizing complex over complete Noetherian local rings. The node is an agent corollary,
  not a misattribution of its whole statement to either tag. Its nine-step proof is
  transcribed in full in the declaration docstring, including homothety compatibility,
  completion descent, maximal-localization descent and the final cone argument.
- No statement fault or STATEMENT-DISPUTED issue was found.

Searches for an existing statement (all via prescribed msearch.py unless stated):

- LeanFinder: "A semidualizing bounded coherent complex over a commutative Noetherian ring
  detects zero objects and isomorphisms under derived Hom". Eight hits, including bounded
  representatives in D(A) and `hasExt_iff`; no semidualizing detection theorem.
- Loogle: `CategoryTheory.MonoidalClosed.curry, CategoryTheory.ihom`. Twelve hits for curry,
  its identities, and the internal-Hom identity map. These provide general closed-category
  operations, not the ring-theoretic theorem. The recorded ringed-site normalized adjunction
  was used instead to stay with the recorded derived-Hom construction.
- LeanSearch: "semidualizing complex derived Hom reflects isomorphisms bounded finite
  cohomology". Eight hits on functors of complexes and short-complex quasi-isomorphisms;
  none is the statement.
- Mathlib grep: `semidualizing|homothety|rhom.*conserv`. Twenty-five results shown, all
  incidental geometric homotheties or affine-map facts, not this theorem.
- Source `rg` for `semidualizing|homothety|rhom.*conserv`: only the unrelated characteristic
  polynomial of a scalar homothety. Source grep of the exact node ID: no result.
- `rg` of the same patterns in `lean/Sheaf`: no result. Broader source searches of derived
  Hom, derived ModuleCat, internal Hom and one-object-site interfaces found the existing
  `RingHomExtensionDefs` and `RingedInternalHomSignedCalculus`, which are reused.
- Read dependency node records in `dag/nodes` and checked `dag/lean_names_upstream.json` for
  matching scalar-action/semidualizing names. No prior declaration of this theorem found.

Validation: the initial complete statement compiled cleanly through scompile.py in both
sandbox and library module positions (2.0 s and 1.9 s). A second compile includes the full
currently recorded proof-import plan. All variables/universes are explicitly bound and
`set_option autoImplicit false` is active. The only postponed proof is the named main
statement. There are no new definitions, helper axioms, file-local instances or notation.

## Second reading by Q07

A separate second pass by this worker reopened the node and module; no additional agent was
started, following the dispatcher's explicit instruction. The maintainer provides the
independent delivery review. This pass checked the two conjuncts, every object quantifier,
all four boundedness/finiteness pairs, the absence of finite-dimension assumptions, and the
identity of the actual scalar-action arrow. In particular, `tensorRight C` requires the
LEFT unitor `λ_ C`, not the right unitor: its input is the unit tensored with C. The stored
signature matches the file verbatim. The one-object evaluation affects only finite generation;
zero objects and morphism isomorphisms remain in the full derived category. No mathematical
mismatch was found and no statement correction was made. This pass also added explicit
private imports for Mathlib proof dependencies whose matches are given by file rather than
by a `lean.module` record. The proof docstring preserves all nine supplied proof steps.
