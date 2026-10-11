## Worker report

The module `Sheaf.Topology.NoetherianCohomologyDimOne` states
`TopCat.Sheaf.isZero_secondCohomology_of_noetherian_dim_le_one`, with proof `sorry`.
No definition is introduced and no theorem is proved.

Hypothesis and conclusion correspondence:

- A topological space X is `(X : Type u) [TopologicalSpace X]`, with explicitly bound universe `u`.
- Noetherian is `[NoetherianSpace X]`. Mathlib defines it as well-founded strict reverse inclusion on opens, equivalent by complements to the node's descending chain condition on closed sets. It imposes neither sobriety nor a separation axiom.
- Topological Krull dimension at most one is `(hdim : topologicalKrullDim X ≤ 1)`. The comparison takes place in `WithBot ℕ∞` and allows dimension minus infinity and zero.
- An arbitrary abelian sheaf is `(F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})`. Its site is all opens of X with open coverings, not an étale site and not a category of quasi-coherent modules.
- The sole conclusion H²(X,F) = 0 is `IsZero (CategoryTheory.Sheaf.H' F 2 (⊤ : Opens X))`. Here H' is an object of AddCommGrpCat, so IsZero means precisely the zero abelian group. The argument ⊤ computes cohomology on the whole space.

Dependency declarations read and used:

- `def-kun-topological-krull-dimension`: `Mathlib.Topology.KrullDimension`, `topologicalKrullDim`. Its full signature and docstring define the supremum of lengths of chains of irreducible closed sets as `krullDim (IrreducibleCloseds X)`.
- `def-sc-topological-abelian-cohomology`: `Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`, `CategoryTheory.Sheaf.H'`. Its section parameters require sheafification and HasExt; its full signature takes an abelian sheaf, a natural degree and an object of the site. The recorded specialization to opens and ⊤ is used verbatim. The auxiliary imports provide sheafification, Grothendieck abelian sheaves, and HasExt automatically; no additional hypotheses for those structures are imposed.

The site has hom universe u, as required by H', and coefficients have universe u. Universe u is arbitrary; spaces and groups of initially different sizes can both be placed in their common larger universe. There is no finite or countable restriction on coefficients.

Edge cases checked mathematically before writing: X empty (dimension ⊥, all cohomology zero); a point and zero-dimensional Noetherian spaces; the two-point spectrum of a DVR (dimension one); F the zero sheaf; reducible and non-sober Noetherian spaces. None is excluded by the binders. The theorem only asserts degree two vanishing, not the stronger title's suggested vanishing in every degree above one.

Source read: [Stacks Proposition 02UZ](https://stacks.math.columbia.edu/tag/02UZ), which asserts exactly the general vanishing for any abelian sheaf on a Noetherian space with dim X ≤ d and p > d. The local literature checkout lacks cohomology.tex, so the source was opened online. The node's one-step proof specializes `lem-sc-noetherian-topological-cohomology-vanishing` to d=1 and q=2; that complete step is carried in the declaration docstring.

Searches for existing declarations:

- `msearch.py leansearch`, query "The second cohomology of every abelian sheaf on a Noetherian topological space of dimension at most one is zero": service UNAVAILABLE (Internal Server Error); no verdict assigned.
- `msearch.py leanfinder`, query "The second cohomology of an abelian sheaf on a Noetherian topological space of Krull dimension at most one vanishes": eight hits, including Sheaf.H and cohomologyPresheaf and unrelated group cohomology; no matching vanishing theorem.
- `msearch.py loogle`, query "Sheaf.H', topologicalKrullDim": unknown short identifier, zero hits. Repeated with "CategoryTheory.Sheaf.H'": H' and Mayer–Vietoris declarations, no dimension vanishing theorem.
- `msearch.py grep`, regex `subsingleton_H_of_topologicalKrullDim|vanishing.*Noetherian|isZero.*[Cc]ohomology`: twelve Mathlib hits, unrelated order-of-vanishing and group cohomology.
- `rg` in WeilConjectures and lean/Sheaf for the item id, `subsingleton_H_of_topologicalKrullDim`, and Noetherian/cohomology patterns: upstream `AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt` concerns scheme modules only; landed `AlgebraicGeometry.isZero_zariskiCohomology_of_dimension_bound` requires a scheme. Neither states the arbitrary topological-space statement. PicardLift only mentions the item in a proof docstring.
- `rg` for the chosen full declaration name in Mathlib, WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json: no collision.

No node correction, missing notion, unusable dependency or statement dispute was found.
Local single-file compilation via lcompile.py succeeded (exit code 0), without warnings.

## Second reading by V1

Read the item node, its Lean module, both statement-dependency nodes, and the actual
Mathlib declarations they record. The source checkout lacks literature/stacks-project;
read [Stacks 02UZ](https://stacks.math.columbia.edu/tag/02UZ) and its
[cohomology.tex source](https://raw.githubusercontent.com/stacks/stacks-project/master/cohomology.tex),
including section-vanishing-Noetherian and proposition-vanishing-Noetherian.
The section imposes no standing separation, sobriety, ring or scheme hypothesis.
Also read Section 01DZ: cohomology is computed from global sections of an injective
resolution in abelian sheaves.

The complete list of objects, hypotheses and conclusion, with the Lean correspondence:

1. X is an arbitrary topological space: `(X : Type u) [TopologicalSpace X]`.
   Verdict: exact; no scheme structure, nonemptiness or separation instance.
2. X is Noetherian, in the descending-closed-chain sense: `[NoetherianSpace X]`.
   Verdict: exact. Mathlib/Topology/NoetherianSpace.lean defines this as
   `WellFoundedGT (Opens X)` and records its equivalence with `WellFoundedLT (Closeds X)`;
   complements reverse inclusion, giving precisely the node's minimal-closed-set condition.
3. Its topological Krull dimension is at most one: `(hdim : topologicalKrullDim X ≤ 1)`.
   Verdict: exact. The dependency def-kun-topological-krull-dimension records
   `topologicalKrullDim`; its actual definition is `krullDim (IrreducibleCloseds X)`
   in `WithBot ℕ∞`. Irreducible closed sets are nonempty, so strict chains have the
   same lengths as the node's definition and the empty space has dimension bottom.
4. F is any abelian sheaf on X:
   `(F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})`.
   Verdict: exact. Read Sites/Spaces.lean: covering sieves cover every point by their
   open domains, so these are ordinary sheaves on the opens of X. No coherent,
   quasi-coherent, constructible or module structure is required.
5. The sole conclusion is H²(X,F) = 0:
   `IsZero (CategoryTheory.Sheaf.H' F 2 (⊤ : Opens X))`.
   Verdict: exact. def-sc-topological-abelian-cohomology records H' at the whole-space
   open. Read the full H' signature and cohomologyPresheafFunctor: this is Ext from
   the sheafified free abelian representable, which at the terminal open represents
   global sections and hence computes the stated derived functors. H' is an
   AddCommGrpCat object, so categorical IsZero is precisely vanishing of this group.
   Its sheafification and Ext instances are supplied by the imports, not additional
   assumptions. All quantifiers occur in the order X, hypotheses, arbitrary F.

Edge cases: the empty space (including the empty scheme's underlying space), dimension
zero, the dimension-one two-point DVR space, reducible and non-sober spaces, and the
zero abelian sheaf are included. There is no index family or coefficient characteristic
hypothesis. Degree is fixed to two; no degree-zero vanishing is asserted. Although the
title mentions every degree above one, the node's statement has only H², and the Lean
correctly has only that clause. Universe u is explicitly bound and arbitrary. H' uses
the opens site's hom universe for coefficients; any differently sized space and sheaf
can be represented in a common larger universe. No smallness or finite coefficient
hypothesis is added.

Independent searches, using different wording from the first reading:

- msearch.py leansearch: "Grothendieck vanishing for second sheaf cohomology on
  noetherian spaces of dimension one": service unavailable, Internal Server Error;
  no mathematical verdict from this service.
- msearch.py leanfinder: "Grothendieck vanishing sheaf cohomology on finite dimensional
  noetherian spaces": eight hits, derived-category degree bounds and Sheaf.H;
  none states the required topological-space vanishing.
- msearch.py loogle: `CategoryTheory.Sheaf.H'`: twelve hits, H' and Mayer-Vietoris
  constructions, no dimension-vanishing theorem. An initial shell-escaped query
  accidentally searched an identifier containing u0027; it was replaced by the
  literal apostrophe query above and supplies no evidence.
- rg across Mathlib, WeilConjectures and lean/Sheaf for Noetherian near cohomology or
  vanishing, isZero_secondCohomology and subsingleton_H_of_topologicalKrullDim:
  no duplicate general topological-space theorem. Opened both close matches:
  Scheme.Modules.subsingleton_H_of_topologicalKrullDim_lt takes a Scheme and an
  O_X-module; AlgebraicGeometry.isZero_zariskiCohomology_of_dimension_bound takes
  a Scheme with compactness and local Noetherian instances. Neither covers this node's
  arbitrary topological spaces. The chosen name also has no upstream-name-table hit.

H4-H9: both recorded dependency declarations are used directly; no definition, private
copy, local notation or hollow data is introduced. The only theorem proof is `sorry`.
The module and theorem docstrings give the source and blueprint id; the theorem's
proof text carries the node's single step, applying the general vanishing node with
bound one and degree two, including empty and zero-dimensional spaces. Imports provide
the stated notions and their categorical instances. Every universe/variable is bound;
lines satisfy the 100-character convention. The node's lean.statement agrees verbatim
with the theorem signature. There are no new nodes, dependency modules or statement
corrections to review.

Mismatches found: none. Changes: appended this independent second-reading report;
the correct Lean module and node record were retained. Local lcompile.py of the module
completed successfully (exit 0, 1.6 seconds), with no warnings or errors.
