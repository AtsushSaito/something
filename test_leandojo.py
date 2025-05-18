#!/usr/bin/env python3
"""
Test script for LeanDojo with the current repository
"""
import os
import subprocess
import lean_dojo
from lean_dojo import LeanGitRepo, trace, Dojo

def print_section(title):
    """Print a section header"""
    print(f"\n{'=' * 50}")
    print(f"  {title}")
    print(f"{'=' * 50}")

def main():
    print_section("LeanDojo Test with Repository")
    print(f"LeanDojo version: {lean_dojo.__version__}")
    
    # Get current directory path
    repo_path = os.path.abspath(os.path.dirname(__file__))
    
    # Get the current commit hash
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"], 
        cwd=repo_path,
        capture_output=True, 
        text=True,
        check=True
    )
    commit_hash = result.stdout.strip()
    
    print(f"Repository path: {repo_path}")
    print(f"Commit hash: {commit_hash}")
    
    try:
        print_section("Creating LeanGitRepo")
        repo = LeanGitRepo(repo_path, commit_hash)
        print(f"Repository created: {repo}")
        
        print_section("Tracing Repository")
        print("This may take a while...")
        traced_repo = trace(repo)
        print("Repository traced successfully")
        
        print_section("Getting Theorems")
        theorems = traced_repo.get_theorems()
        print(f"Found {len(theorems)} theorems:")
        for theorem in theorems:
            print(f"  - {theorem.full_name}")
        
        if theorems:
            print_section("Interacting with Theorem")
            theorem = theorems[0]
            print(f"Selected theorem: {theorem.full_name}")
            
            with Dojo(theorem) as (dojo, state):
                print("\nInitial goal:")
                print(state.pp_goals)
                
                print('\nRunning tactic "rfl"...')
                result = dojo.run_tactic("rfl")
                print(f"Tactic result: {result.status}")
    
    except Exception as e:
        print(f"Error during test: {e}")

if __name__ == "__main__":
    main() 