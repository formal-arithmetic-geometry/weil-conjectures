## Worker report

The module `Sheaf.AlgebraicGeometry.ProEtaleReplete` states
`AlgebraicGeometry.Scheme.isReplete_proEtale`.  It binds an arbitrary scheme
`X : Scheme.{u}` and asserts
`CategoryTheory.GrothendieckTopology.IsReplete.{u + 1, u, w} (Scheme.ProEt.topology X)`
for an arbitrary section universe `w`.  The dependency definition
`CategoryTheory.GrothendieckTopology.IsReplete` expands this to every inverse
sequence functor `F : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X)
(Type (max (u + 1) u w))`, the hypothesis that every adjacent map
`F.map (homOfLE (Nat.le_succ n)).op` is an epimorphism, and the conclusion that
`limit.π F (op m)` is an epimorphism for each `m : ℕ`.  Thus it renders the
node's inverse sequence, all epimorphic transition maps, every projection, and
repleteness clause without adding hypotheses.

The theorem uses the recorded definition rather than making a duplicate
quantifier-based definition. The site has objects in `Type (u + 1)` and
morphisms in `Type u`, so the explicit instantiation is
`IsReplete.{u + 1, u, w}`. Section sets have universe `max (u + 1) w`;
the extra arbitrary `w` imposes no upper bound on their size. Both universes
`u w` and the only object variable `X` are explicitly bound.

The site dependency is Mathlib's `AlgebraicGeometry.Scheme.ProEt` and
`AlgebraicGeometry.Scheme.ProEt.topology` from
`Mathlib.AlgebraicGeometry.Sites.Proetale`.  The repleteness notion is the
project declaration `CategoryTheory.GrothendieckTopology.IsReplete` in
`Sheaf.CategoryTheory.RepleteSheafTopos` (node `det-pe-replete-definition`).
Both dependency records, the complete definition and its docstring, and the
Mathlib site's full declaration and topology were read. The local-surjectivity
proof leaf is `CategoryTheory.Sheaf.isLocallySurjective_iff_epi` from
`Mathlib.CategoryTheory.Sites.LocallySurjective`, already publicly imported by
the repleteness-definition module. The remaining proof nodes
`det-pe-wcb-cover`, `det-pe-weak-contractible-equivalences`, and
`det-pe-replete-on-contractible` currently have neither a Lean record nor a
Mathlib match, so there is no recorded module to import for those proof steps.
They are not missing statement dependencies: their notions do not occur in the
theorem signature. Their four-step use is documented in the theorem docstring.

Edge cases checked against the definition and source: `m = 0` is allowed;
empty section sets pose no extra assumption; the empty scheme is covered by the
same `Scheme.ProEt.topology`; non-quasi-compact and disconnected schemes are
not excluded; constant towers satisfy the same formulation; and no finite
indexing or quasi-compactness hypothesis is introduced.

For an empty `F_m(U)`, local surjectivity at `U` is vacuous; the formulation does
not require global or sectionwise surjectivity. For an empty scheme, the empty
cover condition is retained by Mathlib's topology. A constant tower with identity
transitions has isomorphism projections, as expected. All natural-number
indices, including zero and arbitrary positive indices, occur in `IsReplete`.

Searches made: `msearch.py` leanfinder query “pro-etale site sheaves replete
inverse sequence epimorphic transition maps projection” found only generic
light-condensed/coherent-site results, with no exact match; `msearch.py` loogle
query `CategoryTheory.Sheaf, CategoryTheory.Epi` returned twelve results,
including the cited local-surjectivity criterion, but no sequential-limit
repleteness theorem. Earlier Loogle queries using the project-only
`IsReplete` name or unqualified namespace words were invalid (unknown identifiers),
and are not evidence of absence. `msearch.py` leansearch query “Inverse sequences
of sheaves of sets on the pro etale site have epimorphic limit projections when
transitions are epimorphisms” returned eight results led by the coherent-site
theorem;
`msearch.py` grep query `replete|IsReplete` in `CategoryTheory` found no match;
additional grep searches over `WeilConjectures` and the project found no
exact existing statement and found the dependency definition. The search log is
`searches.jsonl`. Direct `rg` also checked `det-pe-replete-epimorphism` and the
proposed declaration name in the upstream and project Lean sources, and checked
the upstream name index. The results did not duplicate this declaration.
The Mathlib ProEt declaration and its full docstring were read at
`Mathlib/AlgebraicGeometry/Sites/Proetale.lean` lines 100–156.

In particular, the candidate
`CategoryTheory.coherentTopology.epi_π_app_zero_of_epi` was inspected in
`Mathlib/CategoryTheory/Sites/Coherent/SequentialLimit.lean`: it assumes a
preregular finitary extensive category, sequential limits, and the additional
effective-epimorphic projection hypothesis. It is not the scheme-specific node.
The newer shared source
`lean/WeilConjectures/AlgebraicGeometry/ProEtale/Replete.lean` was also searched
and read in full. `AlgebraicGeometry.Scheme.ProEt.epi_π_app_zero_of_epi` there
is about module sheaves, while its concrete-category local-surjectivity theorem
is on the affine site and only concludes epimorphy at zero. Neither declaration
is this node's statement about arbitrary set sheaves on the small pro-étale
site and every index, so no exact existing binding is available.

The current blueprint node and its proof were read directly. The Lean statement
matches them without correction. No statement dispute, new node, dependency
repair, or change outside the item's `lean` record is needed. The only postponed
theorem is `AlgebraicGeometry.Scheme.isReplete_proEtale`, with proof `sorry` and
the full natural-language proof in its docstring; no definition is introduced.

Validation: `scompile.py Q21 det-pe-replete-epimorphism
lean/Sheaf/AlgebraicGeometry/ProEtaleReplete.lean` succeeded for both sandbox and
library module paths. The initial universe mismatch identified the site's
distinct object and morphism universes; it was repaired by the explicit
instantiation above, without equating them.

## Second reading by Q21

I independently read the current node, its blueprint statement and proof, both
statement-dependency records and declarations, all proof-dependency records,
and the delivered Lean module. There is no repair note for this item. The
sandbox node differs from the current shared node only in `lean`; there is no
statement correction, new node, or dependency module to audit.

The source check included Bhatt–Scholze, Definition 3.1.1 (p.16), Definition
3.2.1 and Proposition 3.2.3(1), including its proof (pp.17–18), and Proposition
4.2.8 (p.29), read from the local PDF. The latter says any scheme, without a
quasi-compactness or separation assumption. I also read Stacks `sites.tex`,
Definition `definition-sheaves-injective-surjective` and Lemma
`lemma-mono-epi-sheaves` (00WM–00WN), and `proetale.tex`, Lemmas
`lemma-proetale-enough-w-contractible` and `lemma-weakly-contractible-cover`.
They impose no extra hypothesis on the scheme in this statement. The separate
lifts over covering members need no compatibility on their intersections.

Object/hypothesis/conclusion checklist, expanding the actual recorded definition
`CategoryTheory.GrothendieckTopology.IsReplete`:

1. Every scheme `X`: exactly `(X : Scheme.{u})`, with arbitrary bound `u`.
   Verdict: exact, with no field, characteristic, finiteness, separation, or
   nonemptiness assumption.
2. The small pro-étale site of that same `X`: exactly `ProEt.topology X`.
   I read `Scheme.ProEt`, its all-over-morphisms category, its precoverage, and
   topology in Mathlib `AlgebraicGeometry/Sites/Proetale.lean`. These are the
   objects and fpqc covering topology recorded by `sk-def-pe-site`, not an
   étale site or the affine subsite. Verdict: exact dependency use.
3. An arbitrary inverse sequence of set sheaves: the definition quantifies
   `F : ℕᵒᵖ ⥤ Sheaf J (Type (max u v w))`, instantiated here with site object
   universe `u + 1`, morphism universe `u`, and arbitrary `w`. Thus the section
   universe is `max (u + 1) w`. `F.obj (op n)` is the node's `F_n`; functoriality
   supplies the whole inverse sequence. Verdict: exact; no module coefficients
   or extra structure on the sheaves is assumed.
4. Epimorphic transition maps: exactly
   `∀ n : ℕ, Epi (F.map (homOfLE (Nat.le_succ n)).op)` inside `IsReplete`.
   The arrow has source `F_(n+1)` and target `F_n`. Verdict: exact, and this is
   local surjectivity, not the stronger surjectivity on all sections. I opened
   `Sheaf.isLocallySurjective_iff_epi` in Mathlib `Sites/LocallySurjective.lean`;
   its sheafification size condition is available at the chosen section size.
5. The inverse limit and each coordinate projection: exactly `limit F` and
   `limit.π F (op m)`. I checked `Sheaf.createsLimitsOfShape` in Mathlib
   `Sites/Limits.lean`; its sectionwise construction is the compatible-tuples
   limit in the dependency node. Verdict: the canonical limit and projection.
6. Every projection is epi: exactly `∀ m : ℕ, Epi (limit.π F (op m))`, after
   quantifying `F` and its transition hypothesis. Verdict: all indices in the
   correct order, hence precisely the final repleteness clause as well.

Edge cases: `m = 0` and all positive indices are included. Empty section sets
do not introduce a nonemptiness premise; the lifting test for a target section
is vacuous when there is no such section. The empty scheme and empty site
objects retain their actual topology, including empty covers. Constant towers
and the terminal and initial sheaves are included. The index is specifically
`ℕᵒᵖ`, as in the node and source; arbitrary cofiltered index sets are not
asserted. There is no ring, degree, or characteristic parameter to restrict.
The site's object and morphism universes remain distinct. Arbitrary larger
section universes are covered by `w`; smaller sets admit the usual universe
lift. Both `u` and `w` and the only object variable `X` are explicitly bound.

Independent H4 searches used `msearch.py` with new phrasings: LeanFinder queried
set-valued sheaves on locally weakly contractible sites and countable inverse
systems; LeanSearch queried every natural-number projection on the small
pro-étale site; Loogle used `CategoryTheory.Epi, "limit", "Sheaf"`; grep used
`surjective_π_app_zero|EpiπAppZeroOfEpi|IsReplete`. These searches are recorded in
`searches.jsonl`. Direct `rg` also searched the upstream `WeilConjectures`,
Mathlib sites, and project `lean/Sheaf`, using tower, projective sheaf,
weak-contractibility, sequential epimorphism, and repleteness terminology, and
checked the proposed declaration name against `dag/lean_names_upstream.json`.
No exact existing statement was found.

I inspected the returned Mathlib `Limits.Types.surjective_π_app_zero_of_surjective_map`:
it is about sets with sectionwise surjective transitions, not sheaf epimorphisms.
I also opened `coherentTopology.epi_π_app_zero_of_epi` with its surrounding
assumptions: it requires a preregular finitary extensive coherent-site
presentation and an effective-epimorphic sequential-limit hypothesis. It is
not this scheme theorem. Loogle's four results concern colimits of locally
constant condensed presheaves, not this statement. Finally I read the exact
shared `lean/WeilConjectures/AlgebraicGeometry/ProEtale/Replete.lean`, following
`coord/pefw-upstream-framework.md`. Its ProEt theorem has module coefficients
and projection at zero; its generic concrete-category local-surjectivity
theorem is on AffineProEt. Neither supplies this exact arbitrary-set-sheaf,
arbitrary-index declaration on ProEt.

H5–H9: the delivery introduces no definitions and proves nothing. Its sole
theorem has proof `sorry`; its docstring names the source and blueprint node
and reproduces all four DAG proof steps with their actual dependencies. The
unstated proof nodes still have no recorded modules to import; the local epi
criterion is already imported through the repleteness-definition module. There
are no private copies, file-local notation/instances, unbound variables, or
lines exceeding 100 characters. `lean.statement` was compared programmatically
with the file signature and is verbatim equal.

Mismatches found: none. Changes: appended this second-reading report only;
the correct module and node binding are retained. Validation: the prescribed
`scompile.py Q21 det-pe-replete-epimorphism
lean/Sheaf/AlgebraicGeometry/ProEtaleReplete.lean`, run from the item sandbox,
passed both sandbox and library paths without errors or warnings (1.3 s and
1.4 s respectively).
