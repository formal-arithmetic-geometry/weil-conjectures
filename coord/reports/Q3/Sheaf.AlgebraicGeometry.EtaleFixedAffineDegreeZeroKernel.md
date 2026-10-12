## What changed

Replaced the proof of `AlgebraicGeometry.Etale.fixed_affine_degree_zero_kernel` in
`Sheaf.AlgebraicGeometry.EtaleFixedAffineDegreeZeroKernel`. Its signature and docstring
are unchanged. Added only proof imports: AbelianPullbackGlobalSectionsComparison,
EtaleSetSectionAffineEventualEquality, EtaleCohomologyPullbackDegreeZero, and
WeilConjectures.SixFunctors.BaseChange.GlobalSections.

The proof identifies degree-zero cohomology with global sections, transports the
identity-stage section and zero to the underlying set inverse image, applies existing
affine eventual equality detection at one stage, then transports the equality back. Composition
isomorphisms cancel explicitly. The node records this shorter route.

## Proved and sorry left

Closed in the written proof: `AlgebraicGeometry.Etale.fixed_affine_degree_zero_kernel`
(node `lem-weil-pbc-fixed-affine-degree-zero-kernel`). No holes added or split off.
No sorry remains in the delivered module. This is a proof from existing named
statements, some of which still depend on sorry; it does not close those dependencies.

Validation: the full module compiled with lcompile.py without warnings (28.2 seconds after avoiding rewrite-based comparison transport).
The coefficient-comparison object file became available during the cache refresh.
The complete proof was also checked beforehand in a scratch file with the existing
comparison declaration supplied as a hypothesis; that file is not delivered.
The required delivery dry run is the final validation.

## No longer needed

No existing import was removed: the sole public import is needed by the unchanged
statement. The following former direct proof dependencies are no longer required by
this item (this does not claim that other targets cease to use them):

- `lem-weil-pbc-colimit-initial-full-subcategory` (Mathlib filtered-final lemmas).
- `lem-weil-pbc-affine-etale-site-colimit`, module
  `Sheaf.AlgebraicGeometry.AffineEtaleSiteColimit`.
- `lem-weil-pbc-affine-etale-site-topos`, module
  `Sheaf.AlgebraicGeometry.FullAffineEtaleTopos`.
- `lem-weil-pbc-colimit-constant-connected-diagram` (Mathlib connected colimits).
- `lem-weil-pbc-colimit-of-sites-sections`, module
  `Sheaf.CategoryTheory.ColimitSiteSections`.
- `lem-weil-pbc-filtered-colimit-sets-elementwise` (Mathlib types filtered colimits).

The existing affine eventual-equality theorem applies filtered-colimit equality to
section sets; this proof does not construct a colimit of abelian section groups. No unit statement or unit step
is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original DAG route was longer than necessary. Existing coefficient comparisons
and affine eventual equality detection suffice; no new infrastructure is needed.
The coefficient-comparison module was temporarily absent from the local compiled
cache; the regular refresh resolved it.

## Second reading by Q3

1. Interface: PASS. Compared the complete module with the repository version by
   diff and checked the theorem signature and its docstring byte for byte. Only
   four plain proof imports and the proof body changed. There is no definition,
   new declaration, statement change, or change record.
2. Proof: PASS. Independently compiled the delivered module with lcompile.py
   (31.2 seconds, no warnings). Compiled a scratch copy with `#print axioms
   AlgebraicGeometry.Etale.fixed_affine_degree_zero_kernel` (30.2 seconds): exactly
   `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx`. The last is inherited
   from existing open dependencies, including the coefficient-comparison theorem;
   this delivery removes the item's own hole, not all its transitive holes.
   No sorry or forbidden declaration occurs in the delivered module. The comparison
   witness is eliminated locally in a proposition proof; no arbitrary chosen data
   is placed in a definition or exported object.
3. Split statements: PASS, none. No new modules, nodes, or holes were added. Read
   the existing coefficient comparison, affine eventual equality, and degree-zero
   formula. The comparison is used only via its bijectivity and composition law.
   Zero coefficients and empty affine schemes cause no exception; singleton or
   non-antisymmetric preorders still give equal arrows because hom sets are
   subsingletons. No torsion or nonempty-scheme hypothesis is introduced.
4. Route and pruning: PASS. Read the proof from cohomology down to sections and
   eventual equality; checked the composition-isomorphism cancellations, zero
   transport, and direction of the final opposite arrow. Further repository searches
   for global-section composition, limit comparison, finite-stage killing, and
   fixed pullback descent found the already noted broader continuity route and
   surjectivity theorem; they do not improve this direct reduction. All four added
   imports supply declarations used in the proof, and the sole public import
   supplies its unchanged interface. The six removed old proof dependencies are
   all listed under No longer needed. Read `dag/units/sk-thm-p1.json`: this item is
   below its realized steps, none of which is replaced or bypassed.
5. DAG: PASS. Only `proof`, `proof_deps`, and `proof_origin` changed. The dependency
   list is exactly the union of the steps' uses and matches the three imported
   Sheaf lemmas plus the upstream composition theorem (its primed variant is used).
   The node's statement and Lean record are unchanged. No new-node checks apply.

Second reading changed only this report: recorded the independent interface,
compilation, axioms, mathematical, pruning, and DAG checks. The Lean proof and
node were retained without edits.
