## Worker report

The module defines `AlgebraicGeometry.Scheme.Modules.IsAmple` for an invertible module on a scheme. It states compactness and that every point lies in an affine open represented by the nonvanishing germ locus of a positive tensor power section. The dependencies used are `AlgebraicGeometry.Scheme.Modules.tensorPow` and `AlgebraicGeometry.Scheme.Modules.IsInvertible` from `WeilConjectures.AlgebraicGeometry.Modules.Invertible`, plus Mathlib `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.IsAffineOpen`, and `CompactSpace`. Positive `n` excludes the zero power; no nonemptiness or separation is added. Searches recorded in the node (LeanSearch, LeanFinder, Loogle, grep) found no absolute ampleness declaration; the source `IsAmple` is a different very-ample notion.

## Earlier second reading (a previous round; superseded)

The compactness conjunct renders clause (1). The universal point clause renders positive tensor powers, global sections, affine open nonvanishing loci, and the germ condition in clause (2), with the same objects and no added hypotheses.


## Second reading by K1

I independently opened the node copy, its Lean module, all six statement dependency
nodes and their recorded source signatures. The repository has no local Stacks .tex
checkout, so I read the source on the project server over SSH: properties.tex
4229–4257 (section-ample and definition-ample, Tags 01PR/01PS) and modules.tex
4350–4400 (lemma-s-open, Tag 01CY). These assume an arbitrary scheme and an
invertible module; there is no base field, properness, Noetherian, reducedness,
separatedness or characteristic assumption. The node itself agrees with that source.

The node's objects, hypotheses and clauses, matched item by item:

- Arbitrary scheme X: `X : Scheme.{u}`. Verdict: exact. The dependency
  def-pc-scheme supplies Mathlib's Scheme and Scheme.Hom; IsAffineOpen is the
  affineness of the corresponding open subscheme, not a chosen affine chart.
- An invertible O_X-module L: `L : X.Modules` and `[L.IsInvertible]`. Verdict:
  exact. The recorded dependency declaration in Modules/Invertible.lean says
  that every point has an open neighbourhood where the module is isomorphic to
  the structure sheaf. This is locally free rank one, hence quasi-coherent;
  no extra quasi-coherence assumption needs to be added.
- Tensor powers for n >= 0, with degree zero O_X: `L.tensorPow n`. Verdict:
  exact. I read the source recursion: zero is the monoidal unit and successor
  is L tensor the previous power. Its monoidal structure uses
  `SheafOfModules.monoidalCategory` and `tensorObjIsoSheafification`, both
  declarations recorded by def-pur-sheaf-tensor-product. Thus the source
  tensorPow uses that dependency's tensor product, not a private tensor notion.
  Different association/order from positiveTensorPower is canonically isomorphic.
  Invertibility of powers is the node's pointer, not an extra conclusion or
  missing proof required to construct this Prop-valued definition.
- Global section of the power: `s : (L.tensorPow n).val.presheaf.obj
  (Opposite.op ⊤)`. Verdict: exact, the underlying abelian group of sections
  on all of X, with no finiteness condition.
- Stalk and germ: `TopCat.Presheaf.stalk ... y` and
  `TopCat.Presheaf.germ ... ⊤ y trivial`. Verdict: exact. I read the
  def-weil-pbc-module-stalk match in ModuleCat/Stalk.lean, including the
  CommRingCat module instance and germ_smul. The explicit carrier coercion
  in the Submodule type keeps the stalk in AddCommGrpCat.
- Maximal ideal times the stalk and nonzero residue value: the repaired condition
  is `germ s ∉ (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
  (⊤ : Submodule (X.presheaf.stalk y) ↑(TopCat.Presheaf.stalk ... y))`.
  Verdict: exact after repair. Ideal scalar multiplication of the top submodule
  is m_y (L^n)_y. This uses the node's first definition of X_s directly; it
  need not construct the equivalent tensor-with-residue-field description.
  I also read Scheme.residueField from the residue-field dependency: it is
  precisely IsLocalRing.ResidueField of X.presheaf.stalk y.
- X_s is viewed as an open subscheme: `∃ U : X.Opens` with
  `∀ y : X, y ∈ U ↔ ...`. Verdict: exact. This equality of carriers forces U
  to be the whole nonvanishing locus, not merely an affine subopen inside it.
  Openness is represented by U's bundled topology; no sorry or new openness
  theorem is used, and the source's openness fact remains in the node's pointers.
- Clause (1), X quasi-compact: `CompactSpace X`. Verdict: exact. The dependency
  def-weil-pbc-quasi-compact-scheme uses isCompact_univ without any Hausdorff
  assumption. Compactness is a conjunct, not a typeclass hypothesis on X.
- Clause (2), for each point choose a positive power and section with affine X_s
  containing it: `∀ x : X, ∃ n : ℕ, 0 < n ∧ ∃ s, ∃ U,
  x ∈ U ∧ IsAffineOpen U ∧ ∀ y, ...`. Verdict: exact after the locus repair.
  All choices depend on x in the source's order; IsAffineOpen U is defined as
  IsAffine U in AffineScheme.lean.

Mismatch found (H3): the worker wrote `germ s ≠ 0`, which tests nonzero in the
stalk, not in the fibre. For X = Spec Z, L = O_X and s = 2, its old locus is
all of X, while the correct locus D(2) excludes the point (2). The error also
matters for nilpotents: epsilon on Spec(k[epsilon]/epsilon^2) has nonzero germ
but zero residue value. I replaced this test by nonmembership in m_y times the
stalk module, using the existing Mathlib stalk-module instance and ideal/submodule
operations. I added the required Stalk and Ideal.Operations imports, explained
the locus in the definition docstring, added the conventional copyright header,
and removed the unused Limits namespace opening. No node statement, signature,
dependency record or target was changed. The earlier second-reading paragraph
is explicitly superseded; its germ-condition verdict was incorrect.

Edge cases: the empty scheme is allowed (CompactSpace holds and the point clause
is vacuous); no nonempty index set is introduced. Degree zero exists in tensorPow
but is excluded among witnesses by 0 < n, exactly as the source requires. The
zero section is in m_y times the stalk everywhere and therefore has empty locus.
The zero module is allowed as invertible on the empty scheme; invertibility
already excludes it on a nonempty scheme. Arbitrary characteristic and nonreduced
schemes are included. Universe u is explicitly bound and arbitrary, matching the
scheme/module/tensor APIs; no additional smallness, field or finiteness instance
is introduced. X, L, n, s, U and y are all bound explicitly.

Independent searches (using different descriptions from the first worker):

- msearch LeanFinder: "line bundle sections whose residue values generate affine
  neighbourhoods" returned eight nearby declarations, including
  Scheme.mem_basicOpen'', ModuleCat.Tilde.exists_const and affine-open
  localization lemmas; no absolute ampleness definition.
- msearch LeanSearch: "quasi compact scheme invertible module affine generating
  loci positive powers absolute ampleness" was unavailable (HTTP internal
  server error). This gives no verdict; LeanFinder, Loogle and source searches
  supplied the independent check.
- msearch Loogle: `"IsAmple"` returned zero hits.
- rg of Mathlib/AlgebraicGeometry, WeilConjectures/AlgebraicGeometry and
  lean/Sheaf/AlgebraicGeometry for ample, IsAmple, nonvanishing and
  nonvanishingLocus; further declaration-name searches and a check of
  dag/lean_names_upstream.json found no existing absolute IsAmple.
  I opened the source AlgebraicGeometry.IsAmple: it requires a K-scheme and a
  positive power defining a CLOSED immersion into projective space, so it
  excludes the standard ample structure sheaf on affine one-space and cannot
  serve this node. HasAmpleFamily is a family of potentially different modules,
  not this one-module positive-power condition.
- I also opened Modules/GeneratingLocus.lean: its GeneratesAt and generatingLocus
  express the same nonvanishing locus for an invertible module through local
  free generators. The delivery does not define a second locus notion: it
  retains the direct maximal-ideal predicate already specified by this node
  and merely existentially names the required open. No missing notion,
  new definition node or dependency replacement is needed.

H5/H6/H8/H9: there is one real Prop-valued definition with no sorry, no theorem
or proof added. Both docstrings name the source and blueprint id; the node has
no proof steps to transcribe. All lines are at most 100 characters. The node's
lean.statement remains verbatim the unchanged signature in the file.

Validation: scompile.py K1 def-weil-pbc-ample-invertible-module Ample.lean
compiled the repaired 39-line module on the project server in 1.7 seconds,
exit code 0, with no errors or warnings.
