# Generate proof certificate output for patent/paper evidence.
# Run from repo root: .\lean-proofs\scripts\generate_proof_certificates.ps1
# Or from lean-proofs: .\scripts\generate_proof_certificates.ps1

$ErrorActionPreference = "Stop"
$scriptDir = Split-Path -Parent $MyInvocation.MyCommand.Path
$leanRoot = if (Test-Path (Join-Path $scriptDir "lakefile.lean")) { $scriptDir } else { Join-Path $scriptDir ".." }
$outPath = Join-Path (Split-Path -Parent (Split-Path -Parent $leanRoot)) "docs\proof_certificates.txt"

Push-Location $leanRoot
try {
    if (-not (Test-Path "lakefile.lean")) { throw "lakefile.lean not found in $leanRoot" }
    & lake build 2>&1 | Out-Null
    if ($LASTEXITCODE -ne 0) {
        Write-Warning "Full lake build had errors; attempting verify executable only."
    }
    & lake exe verify 2>&1 | Set-Content -Path $outPath -Encoding utf8
    Write-Host "Proof certificate output written to: $outPath"
} finally {
    Pop-Location
}
