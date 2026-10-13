## What changed

Replaced the single `sorry` in `AlgebraicGeometry.Etale.abelianRawPullback_coherent_base`
with a construction of the actual natural transformations. A generic proved additive
Hom-map construction bundles the five raw factors. A generic proved naturality calculation
uses naturality of upperStarComp and the single-functor comparison, plus map_comp.
Transition and cone-leg maps are obtained by specialization, with the required component
formulas. Extensionality derives the diagram laws from two new, single-class laws.
The existing theorem's signature and public imports are unchanged. No interface adaptation. Repaired the earlier attempt's compile timeout by keeping the
free-sheaf functor factors right-associated and proving additive bundling in arbitrary
preadditive categories; pointwise diagram proofs use a proved presheaf extensionality helper.


Repair of the landing return: removed the private declaration
`AlgebraicGeometry.Etale.pullback_class_naturality`, whose statement duplicated the
private helper in `Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality`.
That existing helper is private and cannot be referenced by importing its module.
The only use now derives the specialized square directly from `c.naturality` and
`t.inv.naturality`, then rewrites functoriality and associativity. No duplicate
statement, visibility change, dependency adaptation, or new import remains.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.Etale.abelianRawPullback_coherent_base`
(node `lem-sbc-abelian-raw-pullback-coherence-base`). The item contains no remaining sorry.

Added two holes, so this is a decomposition, not an axiom-free proof of coherence:

- `AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_identity`, node
  `lem-sbc-abelian-raw-pullback-identity`, module `Sheaf.AlgebraicGeometry.AbelianRawPullbackIdentity`.
- `AlgebraicGeometry.Etale.abelianHigherDirectImageRawPullback_composition`, node
  `lem-sbc-abelian-raw-pullback-composition`, module
  `Sheaf.AlgebraicGeometry.AbelianRawPullbackComposition`.

Both have precisely `:= by sorry`, source references, and full five-factor proof plans.
They concern one class and respectively one or two scheme arrows, with no diagram, cone,
colimit, additive bundling, or naturality conclusion. All bundling and the passage from
pointwise identities to the requested natural-transformation identities are proved in Lean.

## No longer needed

Removed the direct proof imports of `Sheaf.AlgebraicGeometry.DerivedInverseImageComposition`
and `Sheaf.AlgebraicGeometry.AbelianPullbackSingleComposition` from the item. They remain
needed through the new pointwise-law modules; no original dependency node or module is
pruned from the target closure. Removed the unused proof import of
`Sheaf.AlgebraicGeometry.AbelianPullbackSingleComposition` from the new identity module:
its identity calculation uses no composition-on-single lemma. The composition module
still needs it. Kept both original public imports, since the statement
uses the raw presheaf, raw pullback, identity and composition comparisons.

No unit route is bypassed. `dag/units/sk-lem-failure-field.json` has no realized entries
naming this node or its ingredients; the same original structural steps are retained.


Removed the duplicated private naturality helper; its separate local statement is
no longer needed. Importing HigherDirectImageRawOverNaturality would add unrelated
ModuleCat results without making its private helper accessible.

## Where the brief, the DAG or earlier work was wrong

The original plan identifies the correct factors but its listed coherence declarations do
not themselves state the resulting varying-coefficient raw-class identities. In particular,
derivedInverseImageComposition supplies comparison coherence, and
abelianPullbackSingleComposition identifies composition on single objects; neither is the
five-factor class equation. These calculations are now explicit separate tasks.

The existing ModuleCat raw-over pullback lemmas cannot be applied: their coefficients
are restrictions of a single sheaf on a fixed base. They do not cover arbitrary varying
AddCommGrpCat sheaves. No existing statements or definitions were altered. The previous attempt had not completed
a compiling delivery: its grouped generic presheaf source forced expensive functor
associativity checks, and its pointwise calc repeatedly unfolded concrete derived-Hom
objects. The construction now preserves the definition's functor grouping and rewrites
component formulas explicitly; no time limit or library definition was changed.

Mathlib searches: leanfinder found preadditiveYonedaMap for additive Hom bundling;
loogle confirmed its signature. A second leanfinder search for raw identity/composition
found sheafHom and continuous module-sheaf pullback coherence, not this formula;
loogle for mapDerivedCategoryPlusSingleFunctor and grep for the raw laws found no match.
LeanSearch was attempted and returned Internal Server Error. Local rg covered both roots.
Read Stacks Tags 09Z1 and 03CB: the former uses the canonical cohomology comparison
maps in its colimit proof, while the latter provides canonical inverse-image composition.
The new docstrings spell out the structural calculation of original proof step 2.

## New nodes

`lem-sbc-abelian-raw-pullback-identity` states the identity calculation with an explicitly
transported identity scheme arrow and coefficient map. Substitution of the arrow equality
reduces to the canonical identity case. Zero sheaves and classes, empty schemes and p = 0
are allowed; no inverse to a coefficient map is assumed. Its proof plan computes the
identity comparison on single complexes and shifts, uses naturality, then cancels the
single comparisons and inverse-image unit comparison.

`lem-sbc-abelian-raw-pullback-composition` states composition with explicit arrow and
coefficient transports. Substitution of the composite equality reduces to two arbitrary
composable maps. It allows zero or noninvertible coefficient maps, identity arrows, empty
schemes and p = 0. Its proof plan expands the factors, cancels the intermediate single
comparisons, applies derived composition naturality and shift compatibility, and combines
the source and coefficient comparisons. Both nodes inherit the parent's chapter and unit.
No change records are needed because existing interfaces are unchanged.

## Earlier second reading (a previous round; superseded)

1. **Statements and interfaces.** Compared the delivered coherence module byte for byte with the repository version. The existing theorem signature and all existing declarations are unchanged. The two added pointwise theorem signatures match their DAG nodes exactly; no target statement or definition was altered. Verdict: pass.

2. **Proof and trust.** Compiled all three sandbox modules with `lcompile.py --all` and compiled the coherence module directly. The parent theorem has no `sorry`; the only remaining `sorry`s are the two named split-off public theorems. No `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations were added. The parent proof uses only the explicit categorical construction, naturality, and the two pointwise laws. Verdict: pass subject to the two declared open nodes.

3. **New statements.** Checked the identity and composition laws on zero sheaves/classes, identity arrows, empty test objects, and `p = 0`; the statements allow these cases and impose no invertibility assumption on coefficient maps. Searched the local library and Mathlib-oriented search results for duplicate raw-pullback identity/composition declarations; none exists. The two statements are strictly simpler single-class reductions of the parent coherence law and are needed by its final pointwise steps. Verdict: pass.

4. **Pruning and route.** The parent keeps the unit route and constructs the requested natural transformations directly. The old direct proof imports are replaced by the two new pointwise-law modules; the composition module retains `AbelianPullbackSingleComposition`, while the identity module does not import it. Public imports needed by signatures remain public, and proof-only imports are plain imports. Verdict: pass; no additional reachable proof-dependency node can be pruned.

5. **DAG agreement.** The parent node records the actual proof dependencies and the two split nodes record their declarations, source descriptions, proof plans, and module paths. The unit and chapter fields are preserved. Verdict: pass.

Changed during second reading: added this review section only. No Lean proof, declaration, import, or DAG statement required repair.


## Second reading by G3

1. **Unchanged interfaces — pass.** Read the diff of the item against the repository.
   The original theorem signature and docstring are byte-for-byte unchanged, and both
   original public imports remain. Only proof bodies, private construction helpers, and
   proof imports were added or replaced. The identity and composition modules are new;
   no existing definition or target statement changed and no adaptation is delivered.

2. **Proof and trust — pass with the declared holes.** Independently compiled all three
   modules with `lcompile.py --all`: composition 4.4 s, identity 4.9 s, coherence 43.1 s,
   without errors or warnings. Read every construction: homAddMap uses the actual five
   factors, rawPullbackMapGeneral proves naturality directly from c and t, and the
   component formula is definitional. No data is chosen from an existence theorem.
   The only two textual sorries are the whole proofs of the named public split laws.
   A scratch import of the freshly compiled sandbox modules with `#print axioms` for
   all three public theorems reports exactly propext, Classical.choice, Quot.sound,
   and sorryAx. There is no extra axiom or forbidden declaration. The parent therefore
   remains conditional on the two laws, rather than an axiom-free completed proof.

3. **Split statements — pass.** Read both complete docstring calculations against the
   definition of abelianHigherDirectImageRawPullback and the imported coherence and
   single-complex results. After substituting ha/hd, HEq gives precisely the required
   coefficient identity; orientations match the raw source and target factors.
   Zero classes and zero coefficient maps are respected by additive functoriality;
   p = 0 removes shifts, and identity arrows reduce to the unit comparisons. Empty
   schemes introduce no nonemptiness requirement. These are separate single-class
   identity and composition laws, with neither diagram nor naturality/bundling or
   colimit conclusion, and neither restates the item. Both are used by its final
   extensionality steps. Repeated searches with different wording using leanfinder,
   loogle and grep, plus rg on both local roots, found exact-derived-functor shift
   compatibility as an ingredient but no replacement for these equations. Inspected
   HigherDirectImageRawPullbackIdentity and HigherDirectImageRawPullbackCompositionFormula:
   their ModuleCat coefficients come from one fixed sheaf, unlike these varying abelian
   coefficients. Neither remaining calculation is a short direct application of an
   available declaration; no additional hole was closed in this reading.

4. **Route and pruning — pass; reporting clarified.** Checked the original proof_deps
   against the replacement and read dag/units/sk-lem-failure-field.json. Its realized
   statement and step arrays are empty, so no realized node is bypassed. The original
   bundling and coherence steps are retained. The old direct dependency nodes
   lem-weil-pbc-derived-inverse-image-composition and
   lem-sbc-abelian-pullback-single-composition are no longer directly used by the item;
   they remain in the split laws' plans and import closure. Thus there are no modules
   pruned from the target closure. Signature imports are public and added proof imports
   are plain imports. The delivered accounting is one hole closed, two holes added,
   net minus one hole: a decomposition, not net proof progress.

5. **DAG agreement — pass.** Compared the existing node's diff: only proof,
   proof_deps and proof_origin changed. Its steps describe the actual additive/naturality
   construction and the final applications of the two new laws. Checked both new node
   records for source, proof steps, proof_deps, searches, split status, creation fields,
   blueprint ancestry, unit/chapter, module/file and Lean signatures. Their plans match
   their docstrings and their declarations; their dependencies are available.

Changed in this reading: appended this independent review, explicitly named the two
removed direct dependency nodes and clarified the net hole count. No Lean or DAG repair
was necessary. The temporary axiom-check source was removed from the delivery tree.
