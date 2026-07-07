# CLAUDE.md — conventions for all agent sessions in this repo

- UK English. AsciiDoc for docs (`.adoc`), not Markdown (this file and
  the bootstrap prompt are the only exceptions).
- GitHub is the single source of truth; mirrors are spokes.
- No Python. Lean 4 for proofs; shell for glue; Podman if containers
  are ever needed.
- Claim taxonomy: PROVEN / TESTED / ASSUMED / DESIGNED / OPEN.
  Anti-Goodhart clause: a status upgrade must name the transcribable
  artifact that discharges it (build log, eval output, test run).
  Never fabricate identifiers, file contents, or citations.
- Scope discipline: one ROADMAP rung per session. No new features
  outside the rung. No convergence overclaims — agda-routing owns
  that ground (see LIMITATIONS.adoc).
- If a file from the wider estate is needed (e.g. TropicalAdapterPath.lean),
  obtain the real file; never reconstruct it from memory.
- Before ending a session: update STATE.adoc, commit with a message
  naming the rung, and tag only if all gates pass.
- Gates for this repo: `lake build` green; `grep -rn "sorry" Marches/`
  empty; the BadGadget `#eval` prints the period-2 orbit.
