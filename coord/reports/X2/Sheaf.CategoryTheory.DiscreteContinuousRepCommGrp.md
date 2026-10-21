## What changed

Retire Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp, as listed in
coord/retire-items.tsv. Its sole theorem Rep.discreteContinuousRep_commGrp
has a byte-identical docstring, signature and complete proof in
WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrp. The adopted source
library remains unchanged.

Change the sole direct consumer,
Sheaf.AlgebraicGeometry.AbelianSheavesGModulesTransport, by replacing its private
proof import with the upstream twin. Its declarations, proof bodies, public
imports and global instance registrations remain verbatim. In particular it
already publicly imports EtaleFieldGsets and registers
AlgebraicGeometry.etaleFieldDiscreteForget₂ and
AlgebraicGeometry.etaleFieldActionForget₂, covering the difference between the
twin's local instances and the duplicate's global registrations.

Redirect only the existing node lem-exc-discrete-continuous-rep-commgrp's Lean
attachment to the retained upstream declaration, with existing:true. Preserve
its statement, proof, proof dependencies, parents and the sk-prop-h2 unit route.
Withdraw the duplicate using deleted.txt. The change record is
coord/changes/X2-retire-discrete-continuous-rep-commgrp.md, with the complete
17-module downstream closure and claim holders.

## Proved and sorry left

This is a duplicate-retirement repair with zero original holes. Holes closed:
none (0 of 0). Holes added: none. Holes left in delivered modules: none.
Rep.discreteContinuousRep_commGrp was already proved and is retained upstream;
AlgebraicGeometry.Scheme.abelianSheaves_transport retains its complete proof.
No theorem is split off, weakened, renamed or replaced by sorry.

## No longer needed

Pruned module: Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp. Removed import:
import Sheaf.CategoryTheory.DiscreteContinuousRepCommGrp, replaced by
import WeilConjectures.CategoryTheory.DiscreteContinuousRepCommGrp in the sole
consumer. Its duplicate theorem is no longer needed because the identical
upstream theorem supplies exactly the same equivalence and natural comparison.
No mathematical node or declared proof dependency is pruned: in particular
lem-exc-discrete-continuous-rep-commgrp-compatible remains needed by the retained
upstream proof. No source-library declaration is removed. No unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes an item with sorry or an assigned repair.
The live module has zero holes and is explicitly a retirement item, not a new
proof obligation. The existing Lean attachment still names the duplicate; this
packet corrects that attachment without changing the mathematics.

Read Stacks etale-cohomology.tex, lemma-equivalence-abelian-sheaves-point
(Tag 04JQ): a G-module is a G-set with an equivariant commutative group law.
Compared the full theorem signature and proof in both twins byte-for-byte.
Read the compatible-objectwise-isomorphism dependency and the definition of
DiscreteContinuousRep. The current proof still assembles that dependency using
NatIso.ofComponents, exactly as the node records. The zero group, trivial action,
arbitrary carrier universes, chosen Cartesian structures and non-Hausdorff
topological groups retain exactly the same hypotheses and conclusion.

Mathlib searches ran through msearch.py using LeanFinder, Loogle and grep.
LeanFinder returned discrete-action definitions and Galois-category results;
Loogle returned zero hits; grep returned general internal-group and exact-limit
facts. The exact match is the proved source-library twin found by repository rg.
No new statement or node is needed. tools/import_direction.py confirms the
consumer's replacement import introduces no cycle.

The adapted consumer compiled cleanly through lcompile.py on the project server
in 6.2 seconds, with exit code 0 and no warnings. Its only edit is the private
import substitution. Node comparison confirms only the lean field changed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
